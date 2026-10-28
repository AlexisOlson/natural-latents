"""PACK-REFREEZE shared pieces: the exact 2^-52 grid law (out/pb/law.json), block costs and penalized residuals on
that grid, the stored pool plus PACK-BOUND's witnesses, and the symmetrised pool LP (HiGHS, persistent model).
Search-phase float64 throughout: nothing here is a certificate."""
import os, sys, json, pathlib, hashlib
for k in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMBA_NUM_THREADS'):
    os.environ.setdefault(k, '1')
RF = pathlib.Path(__file__).resolve().parent
OUT = RF.parent
PB = OUT / 'pb'
sys.path.insert(0, str(OUT / 'eng'))
sys.path.insert(0, str(PB / 'baseline'))
sys.path.insert(0, str(PB))
import numpy as np
from numba import njit

BIG = 5.0


def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def load_law():
    law = json.loads((PB / 'law.json').read_text())
    n = law['n']; den = 1 << law['denom_log2']
    ROW = np.repeat(np.arange(n), n).astype(np.int64); COL = np.tile(np.arange(n), n).astype(np.int64)
    diff = (COL - ROW) % n; DIST = np.minimum(diff, n - diff).astype(np.int64)
    pint = np.array(law['p_int'], dtype=np.int64)[diff]
    P = pint.astype(float) / den
    return dict(n=n, den=den, pint=pint, P=P, ROW=ROW, COL=COL, DIST=DIST, nd=int(DIST.max()) + 1,
                size=np.bincount(DIST).astype(float), law=law)


def load_windows(price):
    lo = np.array(price['lo'], np.int64); hi = np.array(price['hi'], np.int64); U2 = int(price['U2'])
    we = np.concatenate([[0.0], hi / U2]).astype(float)
    return lo, hi, U2, we


def hv(v):
    v = np.asarray(v, float).ravel(); v = v[v > 0]
    return float(-(v * np.log(v)).sum())


def block_cost(mask, L):
    P = L['P']; n = L['n']
    r = np.bincount(L['ROW'][mask], weights=P[mask], minlength=n); c = np.bincount(L['COL'][mask], weights=P[mask], minlength=n)
    m = P[mask].sum()
    return 2 * hv(r) + 2 * hv(c) - hv([m])


def block_window(mask, L, hi, U2):
    """exact: window t with lo_t/U2 < m <= hi_t/U2 on the grid (integer comparison)."""
    mi = int(L['pint'][mask].sum())
    return int(np.searchsorted(hi * L['den'], mi * U2, side='left'))


@njit(cache=True)
def hf(s):
    if s <= 0.0:
        return 0.0
    return -s * np.log(s)


@njit(cache=True)
def phi_rob(M, we, wv):
    """largest phi over windows whose 1e-12-widened closure contains M."""
    K = wv.shape[0]
    j = np.searchsorted(we, M, side='left') - 1
    if j < 0:
        j = 0
    if j >= K:
        j = K - 1
    v = wv[j]
    if j + 1 < K and we[j + 1] - M <= 1e-12:
        v = max(v, wv[j + 1])
    if j - 1 >= 0 and M - we[j] <= 1e-12:
        v = max(v, wv[j - 1])
    return v


@njit(cache=True)
def resid_rob(mask, P, ROW, COL, gam, n, we, wv):
    r = np.zeros(n); c = np.zeros(n); m = 0.0; g = 0.0; cnt = 0
    for z in range(mask.shape[0]):
        if mask[z]:
            r[ROW[z]] += P[z]; c[COL[z]] += P[z]; m += P[z]; g += gam[z]; cnt += 1
    if cnt == 0:
        return 1e300
    t = 0.0
    for i in range(n):
        t += 2 * hf(r[i]) + 2 * hf(c[i])
    return t - hf(m) - g - phi_rob(m, we, wv)


@njit(cache=True)
def resid_many(masks, P, ROW, COL, gam, n, we, wv):
    out = np.empty(masks.shape[0])
    for b in range(masks.shape[0]):
        out[b] = resid_rob(masks[b], P, ROW, COL, gam, n, we, wv)
    return out


def witnesses():
    """PACK-BOUND's 16 witness blocks (12 simplified band blocks + 4 search violators)."""
    out = []
    simple = json.loads((PB / 'simplified_obstructions.json').read_text())['simple']
    for s in simple:
        out.append((f"band{s['width']}_minus{s['removed']}", s['cells']))
    for f in ('violator_d0_ALL.json', 'violator_d0_L29.json', 'repaired_violator_d0_L10.json', 'repaired_violator_d0_L15.json'):
        out.append((f, json.loads((PB / f).read_text())['cells']))
    return out


def stored_pool():
    with np.load(PB / 'frozen_pool.npz', allow_pickle=False) as d:
        masks = np.unpackbits(d['cols'], axis=1)[:, :900].astype(bool)
        return masks, [np.asarray(q, np.int64) for q in d['pats']], float(d['H3']), float(d['tau'])


def canon_key(mask, n):
    M = mask.reshape(n, n); best = None
    for MM in (M, M.T):
        for a in range(n):
            k = np.roll(np.roll(MM, -a, 0), -a, 1).tobytes()
            if best is None or k < best:
                best = k
    return best


class PoolLP:
    """min sum c(U) x_U s.t. orbit counts = size_d (gamma_d), window balance (phi_t), sum y_P = 1 (sigma),
    ray -e_0 (phi_0 >= 0), and with cap=True +e_t for every t (phi_t <= 0)."""

    def __init__(self, L, price_windows, cap=True, g15max=None):
        import highspy
        self.L = L; self.lo, self.hi, self.U2, self.we = price_windows; self.K = len(self.lo); self.cap = cap
        nd = L['nd']; K = self.K; self.nd = nd
        h = highspy.Highs(); h.setOptionValue('output_flag', False); h.setOptionValue('threads', 1)
        rhs = np.concatenate([L['size'], np.zeros(K), [1.0]])
        h.addRows(nd + K + 1, rhs, rhs.copy(), 0, np.array([0], dtype=np.int32), np.array([], dtype=np.int32), np.array([]))
        inf = highspy.kHighsInf
        h.addCol(0.0, 0.0, inf, 1, np.array([nd], dtype=np.int32), np.array([-1.0]))       # phi_0 >= 0
        if cap:
            for t in range(K):
                h.addCol(0.0, 0.0, inf, 1, np.array([nd + t], dtype=np.int32), np.array([1.0]))   # phi_t <= 0
        if g15max is not None:      # gamma_{nd-1} <= g15max
            h.addCol(float(g15max), 0.0, inf, 1, np.array([nd - 1], dtype=np.int32), np.array([1.0]))
        self.h = h; self.inf = inf
        self.cols = []; self.keys = set(); self.costs = []; self.wins = []; self.cnts = []; self.colpos = []
        self.pats = []; self.patkeys = set(); self.ncolh = h.getNumCol()

    def add(self, mask):
        mask = np.asarray(mask, bool)
        if not mask.any():
            return False
        k = canon_key(mask, self.L['n'])
        if k in self.keys:
            return False
        self.keys.add(k)
        c = block_cost(mask, self.L); w = block_window(mask, self.L, self.hi, self.U2)
        cn = np.bincount(self.L['DIST'][mask], minlength=self.nd)
        idx = list(np.nonzero(cn)[0]) + [self.nd + w]; val = [float(cn[d]) for d in np.nonzero(cn)[0]] + [1.0]
        self.h.addCol(float(c), 0.0, self.inf, len(idx), np.array(idx, dtype=np.int32), np.array(val))
        self.cols.append(mask.copy()); self.costs.append(c); self.wins.append(w); self.cnts.append(cn)
        self.colpos.append(self.ncolh); self.ncolh += 1
        return True

    def add_pat(self, P):
        P = np.asarray(P, np.int64); key = P.tobytes()
        if key in self.patkeys:
            return False
        self.patkeys.add(key); self.pats.append(P.copy())
        nz = np.nonzero(P)[0]
        idx = [self.nd + int(t) for t in nz] + [self.nd + self.K]; val = [-float(P[t]) for t in nz] + [1.0]
        self.h.addCol(0.0, 0.0, self.inf, len(idx), np.array(idx, dtype=np.int32), np.array(val)); self.ncolh += 1
        return True

    def solve(self):
        import highspy
        from cg import price_patterns
        while True:
            self.h.run()
            st = self.h.getModelStatus()
            if st != highspy.HighsModelStatus.kOptimal:
                raise RuntimeError(f'HiGHS status {st}')
            sol = self.h.getSolution(); du = np.array(sol.row_dual)
            self.val = self.h.getInfo().objective_function_value
            nd, K = self.nd, self.K
            self.gam = du[:nd].copy(); phi = du[nd:nd + K].copy(); self.sigma = du[nd + K]
            occ = sorted(set(self.wins))
            cost = phi.copy()
            if not self.cap:
                mask = np.full(K, True); mask[occ] = False; cost[mask] = 1e300
            v, P = price_patterns(cost, self.lo, self.hi, self.U2)
            if v - self.sigma < -1e-9 and self.add_pat(P):
                continue
            break
        self.phi = phi
        if not self.cap:
            self.phi_sep = np.full(K, BIG); self.phi_sep[occ] = phi[occ]
        else:
            self.phi_sep = phi.copy()
        xs = np.array(sol.col_value); self.x = xs[np.array(self.colpos, dtype=np.int64)]
        return self.val

    def T(self, H3, tau):
        return (self.val - H3) / tau
