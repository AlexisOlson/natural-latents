"""PACK-REPLAY-V4 independent leaf checker (standard library only; run as `python -I checker.py ...`).

Reads JSON only: the grid law, the price, the transfer, the stored leaf paths and the proposer's certificates.
Derivation of every inequality: CHECKER.md. Nothing from the engine is imported; the end of every run asserts so.

usage:
  python -I checker.py chunk  LAW PRICE TRANSFER FAMILY_INDEX LEAVES.json.gz START END CERTS.jsonl.gz OUT.json [BUMP]
  python -I checker.py kraft  FAMILY_INDEX LEAVES.json.gz OUT.json          (prefix code + family name)
  python -I checker.py consts LAW PRICE TRANSFER                            (E_block check, constants, d15 sign)
"""
import sys, os, json, gzip, time, hashlib
from fractions import Fraction as Q

N = 30
K = 96                       # fixed-point scale: integers in units of 2^-K
ONE = 1 << K
WD = 1 << 40                 # certificate weight denominator
TB = 17                      # log table: top TB bits of the argument

FORBIDDEN = ('cover', 'final', 'common', 'fastcoef', 'fastenv', 'fastlog', 'fast_integer_node_engine',
             'fast_integer_family', 'fast_integer_elementary', 'fast_integer_small', 'rational_law', 'repair',
             'runtime', 'roots', 'numpy', 'numba', 'scipy', 'pen', 'core')


def set_below_normal():
    if os.name == 'nt':
        import ctypes
        k = ctypes.windll.kernel32
        k.GetCurrentProcess.restype = ctypes.c_void_p
        k.SetPriorityClass.argtypes = [ctypes.c_void_p, ctypes.c_uint32]
        k.GetPriorityClass.argtypes = [ctypes.c_void_p]
        k.GetPriorityClass.restype = ctypes.c_uint32
        h = k.GetCurrentProcess()
        if not k.SetPriorityClass(h, 0x4000) or k.GetPriorityClass(h) != 0x4000:
            raise RuntimeError('BelowNormal priority not verified')


def independence_assertion():
    bad = sorted(m for m in sys.modules if m.split('.')[0] in FORBIDDEN)
    assert not bad, bad
    return 'no forbidden module in sys.modules (%d modules loaded; checked: %s)' % (len(sys.modules), ','.join(FORBIDDEN))


# ---------------------------------------------------------------------------------------------------------------
# Outward natural logarithms in fixed point.  Every function returns integers (lo, hi) with
#   lo * 2^-K <= ln(.) <= hi * 2^-K.
# ln(1+u), 0 <= u <= 1/2:  u - u^2/2 + u^3/3 - u^4/4 <= ln(1+u) <= u - u^2/2 + u^3/3   (alternating series).
# atanh series for the table: ln(y) = 2 sum_{j>=0} z^(2j+1)/(2j+1), z = (y-1)/(y+1) in [0, 1/3]; the omitted
# tail after J terms is positive and at most 2 z^(2J+1) / ((2J+1)(1 - z^2)) <= 2 z^(2J+1) * (9/8).
# ---------------------------------------------------------------------------------------------------------------
GP = 140                                   # guard precision for table construction


def _ln_ratio_guard(num, den, prec=GP):
    """(lo, hi) of ln(num/den) for 1 <= num/den <= 2, in units 2^-prec, by the atanh series."""
    zn, zd = num - den, num + den          # z = zn/zd in [0, 1/3]
    if zn == 0:
        return 0, 0
    S = 1 << prec
    acc_lo = 0; acc_hi = 0
    zpow_n, zpow_d = zn, zd                # z^(2j+1)
    j = 0
    while True:
        t = (2 * S * zpow_n) // ((2 * j + 1) * zpow_d)            # floor of 2 z^(2j+1)/(2j+1) * S
        acc_lo += t; acc_hi += t + 1
        zpow_n *= zn * zn; zpow_d *= zd * zd; j += 1
        tail = -((-(9 * 2 * S * zpow_n)) // (8 * zpow_d))        # ceil of (9/8) 2 z^(2j+1) S (j already advanced)
        if tail <= 4:
            return acc_lo, acc_hi + tail


def _build_tables():
    l2lo, l2hi = _ln_ratio_guard(2, 1)
    sh = GP - K
    LN2 = (l2lo >> sh, -((-l2hi) >> sh))
    lo_t = []; hi_t = []
    base = 1 << (TB - 1)
    for idx in range(base, 2 * base):
        a, b = _ln_ratio_guard(idx, base)                         # ln(idx / 2^(TB-1))
        a = (a >> sh) + (TB - 1) * LN2[0]; b = -((-b) >> sh) + (TB - 1) * LN2[1]
        lo_t.append(a); hi_t.append(b)
    return LN2, lo_t, hi_t


LN2, LNLO, LNHI = _build_tables()
TBASE = 1 << (TB - 1)


def ln_int(r):
    """outward ln(r) for an integer r >= 1."""
    b = r.bit_length(); s = b - TB
    if s <= 0:
        idx = r << (-s)                                           # ln r = ln idx + s ln2, s <= 0
        return LNLO[idx - TBASE] + s * LN2[1], LNHI[idx - TBASE] + s * LN2[0]
    idx = r >> s; d = r - (idx << s)
    lo = LNLO[idx - TBASE] + s * LN2[0]; hi = LNHI[idx - TBASE] + s * LN2[1]
    if d:
        m = idx << s                                              # u = d/m in [0, 2^-(TB-1))
        U0 = (d << K) // m; U1 = U0 + 1                           # U0 <= u*2^K <= U1
        sq0 = U0 * U0; sq1 = U1 * U1
        cu0 = sq0 * U0; cu1 = sq1 * U1
        # lower: u - u^2/2 + u^3/3 - u^4/4, each term rounded down using the right endpoint
        lo += U0 - (sq1 >> (K + 1)) - 1 + (cu0 // (3 << (2 * K))) - ((sq1 * sq1) >> (3 * K + 2)) - 1
        # upper: u - u^2/2 + u^3/3
        hi += U1 - (sq0 >> (K + 1)) + (cu1 // (3 << (2 * K))) + 2
    return lo, hi


def ln_frac(q):
    """outward ln of a positive Fraction."""
    a = ln_int(q.numerator); b = ln_int(q.denominator)
    return a[0] - b[1], a[1] - b[0]


def ln_frac_hp(q, prec):
    """outward ln of a positive Fraction in units 2^-prec (high precision, for one-off checks)."""
    num, den = q.numerator, q.denominator
    k = num.bit_length() - den.bit_length()
    if (num << max(0, -k)) < (den << max(0, k)):
        k -= 1                                                   # now 2^k <= q < 2^(k+1)
    yn, yd = (num, den << k) if k >= 0 else (num << -k, den)
    a, b = _ln_ratio_guard(yn, yd, prec)
    l2a, l2b = _ln_ratio_guard(2, 1, prec)
    return (a + k * l2a, b + k * l2b) if k >= 0 else (a + k * l2b, b + k * l2a)


class Grid:
    """h(t) = -t ln t on grid masses t = r / 2^DL, outward, memoized by the integer r."""

    def __init__(self, DL):
        self.DL = DL
        self.c_lo = DL * LN2[0]; self.c_hi = DL * LN2[1]          # ln(2^DL)
        self.memo = {}

    def h(self, r):
        v = self.memo.get(r)
        if v is not None:
            return v
        if r == 0:
            v = (0, 0)
        else:
            a, b = ln_int(r)                                     # -ln t = DL ln2 - ln r >= 0 when r <= 2^DL
            v = ((r * (self.c_lo - b)) >> self.DL, -((-(r * (self.c_hi - a))) >> self.DL))
        if len(self.memo) > 4_000_000:
            self.memo.clear()
        self.memo[r] = v
        return v


def ceil_fx(q):
    return -((-q.numerator << K) // q.denominator)


def floor_fx(q):
    return (q.numerator << K) // q.denominator


# ---------------------------------------------------------------------------------------------------------------
# Root families (own reimplementation from roots.py's prose: docstring lines 1-11, comments 43-46 and 105-110)
# ---------------------------------------------------------------------------------------------------------------
def cyc_dist(n, z):
    i, j = divmod(z, n); k = (j - i) % n
    return min(k, n - k)


def families(n):
    """list of (name, d, on, off, line, clauses); a clause is (tuple of cells in cyclic order, forbidden value)."""
    out = []
    for d in range(n // 2, -1, -1):
        line = [(t % n) * n + ((t + d) % n) for t in range(n)]
        below = [z for z in range(n * n) if cyc_dist(n, z) < d]
        out.append((f'd{d}_ALL', d, sorted(line), sorted(below), line, []))
        for L in range(1, n):
            runs = [(tuple(line[(t + s) % n] for s in range(L + 1)), 1) for t in range(n)]      # no run longer than L
            if L >= 2:
                off = set(below) | {line[L % n], line[n - 1]}
                out.append((f'd{d}_L{L}', d, sorted(line[:L]), sorted(off), line, runs))
                continue
            for G in range(1, n):
                on = {line[0]}; off = set(below) | {line[t] for t in range(1, G + 1)} | {line[n - 1]}
                if G + 1 <= n - 1:
                    if line[G + 1] in off:
                        continue
                    on.add(line[G + 1])
                gaps = [(tuple(line[(t + s) % n] for s in range(G + 1)), 0) for t in range(n)]  # no gap longer than G
                out.append((f'd{d}_L1_G{G}', d, sorted(on), sorted(off), line, runs + gaps))
    return out


def propagate(val, clauses):
    """unit propagation to fixpoint.  val: dict cell -> 0/1 for assigned cells (mutated).  Returns vacuous?"""
    changed = True
    while changed:
        changed = False
        for S, f in clauses:
            free = None; nfree = 0; sat = False
            for z in S:
                v = val.get(z)
                if v is None:
                    nfree += 1; free = z
                    if nfree > 1:
                        break
                elif v != f:
                    sat = True; break
            if sat or nfree > 1:
                continue
            if nfree == 0:
                return True                                      # all of S equals f
            val[free] = 1 - f; changed = True
    return False


def rebuild(fam, path):
    """returns (vacuous, val, notes).  notes counts path steps on cells already assigned by propagation."""
    name, d, on, off, line, clauses = fam
    val = {z: 1 for z in on}
    for z in off:
        assert z not in val
        val[z] = 0
    lineset = set(line)
    vac = propagate(val, clauses)
    notes = []
    for step, (z, bit) in enumerate(path):
        assert bit in (0, 1) and 0 <= z < N * N
        if vac:
            notes.append(('after_vacuous', step)); continue
        if z in val:
            notes.append(('preassigned', step, z, bit, val[z]))
            if val[z] != bit:
                vac = True
            continue
        val[z] = bit
        if z in lineset:
            vac = propagate(val, clauses)
    return vac, val, notes


def kraft(paths):
    """complete binary prefix code with consistent branch variables; returns max depth."""
    seen = set(); branch = {}; kids = {}
    maxlen = max(len(p) for p in paths)
    total = 0
    for p in paths:
        p = tuple((int(z), int(b)) for z, b in p)
        assert p not in seen, 'duplicate leaf'
        seen.add(p)
        cells = [z for z, _ in p]
        assert len(set(cells)) == len(cells), 'cell repeated on a path'
        total += 1 << (maxlen - len(p))
        pre = ()
        for z, b in p:
            assert b in (0, 1)
            if branch.setdefault(pre, z) != z:
                raise AssertionError('inconsistent branch variable')
            kids.setdefault(pre, set()).add(b)
            pre = pre + ((z, b),)
    assert total == 1 << maxlen, 'Kraft sum %r' % Q(total, 1 << maxlen)
    assert not (seen & set(branch)), 'a leaf is an internal node'
    assert all(v == {0, 1} for v in kids.values()), 'missing child'
    return maxlen


# ---------------------------------------------------------------------------------------------------------------
# The leaf bound
# ---------------------------------------------------------------------------------------------------------------
class Checker:
    def __init__(self, law, price, transfer):
        self.n = law['n']; assert self.n == N
        self.DL = law['denom_log2']
        pint = [int(v) for v in law['p_int']]
        assert len(pint) == N and all(v >= 0 for v in pint)
        self.P = [pint[(z % N - z // N) % N] for z in range(N * N)]          # P[30i+j] = p_int[(j-i) mod 30]
        self.ROW = [z // N for z in range(N * N)]; self.COL = [z % N for z in range(N * N)]
        self.gq = [Q(price['gamma'][cyc_dist(N, z)]) for z in range(N * N)]  # exact binary64 rationals
        self.gceil = [ceil_fx(g) for g in self.gq]
        lo, hi, U2 = price['lo'], price['hi'], price['U2']
        assert len(lo) == len(hi) == len(price['phi']) and lo[0] == 0 and hi[-1] == U2 and lo[1:] == hi[:-1]
        assert all(a < b for a, b in zip(lo, hi))
        self.phi_q = [Q(v) for v in price['phi']]
        self.phi_ceil = [ceil_fx(v) for v in self.phi_q]
        self.delta = Q(transfer['delta']); self.error = Q(transfer['error'])
        assert 0 < self.delta < Q(1, 4)
        self.err_ceil = ceil_fx(self.error)
        D = 1 << self.DL
        # widened closed windows [lo/U2 - Delta, hi/U2 + Delta] in grid units, rounded outward to integers
        self.wlo = [((Q(a, U2) - self.delta) * D).__floor__() for a in lo]
        self.whi = [((Q(b, U2) + self.delta) * D).__ceil__() for b in hi]
        self.nwin = len(lo)
        self.grid = Grid(self.DL)

    # windows whose widened closure meets [a, b] (grid integers), each with the clipped interval
    def windows(self, a, b):
        # wlo, whi are nondecreasing; scan from the first window whose upper edge reaches a
        lo_, hi_ = 0, self.nwin
        while lo_ < hi_:
            mid = (lo_ + hi_) // 2
            if self.whi[mid] < a:
                lo_ = mid + 1
            else:
                hi_ = mid
        j = lo_
        while j < self.nwin and self.wlo[j] <= b:
            yield j, max(a, self.wlo[j]), min(b, self.whi[j])
            j += 1

    def node_bound(self, val, fz_claimed, orders, weights):
        """lower bound (units 2^-K) on min over completions of grid residual(U); see CHECKER.md.
        val: logical assignment (cell -> 0/1).  Returns (bound, info)."""
        P, ROW, COL, grid = self.P, self.ROW, self.COL, self.grid
        on = [z for z in range(N * N) if val.get(z) == 1]
        fz = []
        for z in range(N * N):
            if z in val:
                continue
            if P[z] == 0:
                assert self.gq[z] <= 0, 'free zero cell with positive gamma'
                continue                                          # bound-only omission (PROOF.txt section 4)
            fz.append(z)
        if fz_claimed is not None and fz_claimed != fz:
            raise AssertionError('free set differs from the proposer node')
        r0 = [0] * N; c0 = [0] * N; m0 = 0; g0 = Q(0)
        for z in on:
            r0[ROW[z]] += P[z]; c0[COL[z]] += P[z]; m0 += P[z]; g0 += self.gq[z]
        base = 0
        for v in r0 + c0:
            base += 2 * grid.h(v)[0]
        base -= ceil_fx(g0)
        k = len(fz)
        if k == 0:
            if m0 == 0:
                psi = 0
            else:
                psi = -grid.h(m0)[1]                              # M ln M >= -h_hi(M)
            ph = max(self.phi_ceil[j] for j, _, _ in self.windows(m0, m0))
            return base + psi - ph, dict(k=0, pieces=1)
        # certificate shape
        assert len(orders) == len(weights) > 0
        assert all(type(w) is int and w >= 0 for w in weights) and sum(weights) == WD, 'bad weights'
        accum = [0] * k
        ident = list(range(k))
        pz = [P[z] for z in fz]; rz = [ROW[z] for z in fz]; cz = [COL[z] for z in fz]; gz = [self.gceil[z] for z in fz]
        h = grid.h
        r0h = [h(v)[1] for v in r0]; c0h = [h(v)[1] for v in c0]
        for order, w in zip(orders, weights):
            if sorted(order) != ident:
                raise AssertionError('invalid permutation')
            if not w:
                continue
            r = r0[:]; c = c0[:]; rh = r0h[:]; ch = c0h[:]                # rh/ch: upper h of the current marginal
            for e in order:
                p = pz[e]; i = rz[e]; j = cz[e]
                rn = r[i] + p; cn = c[j] + p
                hr = h(rn); hc = h(cn)
                accum[e] += w * (2 * (hr[0] - rh[i]) + 2 * (hc[0] - ch[j]) - gz[e])
                r[i] = rn; c[j] = cn; rh[i] = hr[1]; ch[j] = hc[1]
        x = [a // WD for a in accum]                              # floor: x_e <= sum_o w_o v^o_e / WD
        # fractional knapsack by x_e/p_e ascending (exact key: distinct ratios differ by > 2^-106)
        idx = sorted(range(k), key=lambda e: (x[e] << 107) // pz[e])
        best = None; pieces = 0; mu = m0; sx = 0
        DL = self.DL
        for e in idx:
            p = pz[e]; xe = x[e]
            a = mu; b = mu + p
            rho = xe / p * 2.0 ** (DL - K)                        # float, only to choose the tangent point
            for j, lo, hi in self.windows(a, b):
                pieces += 1
                lo = max(lo, a); hi = min(b, hi)
                if lo > hi:
                    continue
                cand = []
                if hi == 0:
                    # M = 0 only: M ln M = 0 exactly
                    cand.append((xe * (0 - a)) // p)
                else:
                    # tangent point q (any positive dyadic); M ln M >= (1 + ln q) M - q for all M >= 0
                    ex = -1.0 - rho
                    try:
                        qf = 2.718281828459045 ** ex if ex < 700 else float('inf')
                    except OverflowError:
                        qf = float('inf')
                    qi = int(qf * 2.0 ** DL) if qf * 2.0 ** DL < 2.0 ** 1000 else hi
                    qi = max(lo, min(hi, qi))
                    if qi <= 0:
                        qi = 1 if hi >= 1 else hi
                    # q = qi / 2^DL; ln q >= ln_lo(qi) - DL ln2_hi
                    lq = ln_int(qi)[0] - DL * LN2[1]
                    q_hi = -((-(qi << K)) >> DL)
                    for M in (lo, hi):
                        lin = (xe * (M - a)) // p                 # floor(rho (M - a)) in K units
                        tan = ((ONE + lq) * M) >> DL              # floor((1 + ln q) M)
                        cand.append(lin + tan - q_hi)
                v = base + sx + min(cand) - self.phi_ceil[j]
                if best is None or v < best:
                    best = v
            mu = b; sx += xe
        assert best is not None
        return best, dict(k=k, pieces=pieces)

    def eblock_upper(self):
        """upper bound on 4n h(Delta/n) + h(Delta), own logarithms."""
        def h_hi(t):
            lo, _ = ln_frac_hp(t, 400)                           # -t ln t <= t * (-ln_lo t)
            return Q(-lo, 1 << 400) * t
        return 4 * N * h_hi(self.delta / N) + h_hi(self.delta)


def check_node(C, fam, c, res):
    """check one certificate entry; returns (accepted, margin or None, reason)."""
    path = [tuple(q) for q in c['path']]
    vac, val, notes = rebuild(fam, path)
    res['preassigned_steps'] += sum(1 for nt in notes if nt[0] == 'preassigned')
    if vac:
        res['vacuous'] += 1
        return True, None, 'vacuous'
    if c.get('vacuous'):
        return False, None, 'certificate says vacuous; rebuilt node is not'
    try:
        assert sorted(z for z, v in val.items() if v == 1) == c['on'], 'on set differs from the proposer node'
        b, info = C.node_bound(val, c['fz'], c['orders'], c['weights'])
    except (AssertionError, KeyError, TypeError) as ex:
        return False, None, 'malformed: %r' % (ex,)
    margin = Q(b, ONE) - C.error                                   # accept iff > 0
    return margin > 0, margin, 'bound'


def load_slice(leavesf, s, e):
    """stored leaves s..e-1 of a family's leaf file, without building the other ~1.3M (equals json.load(...)[s:e])."""
    text = gzip.open(leavesf, 'rt').read()
    assert text[0] == '['
    dec = json.JSONDecoder(); pos = 1; i = 0; out = []
    while i < e:
        while text[pos] in ' \n\r\t,':
            pos += 1
        if text[pos] == ']':
            break
        obj, pos = dec.raw_decode(text, pos)
        if i >= s:
            out.append(obj)
        i += 1
    assert len(out) == e - s, 'leaf file shorter than the job range'
    return out


def check_chunk(argv):
    """certify stored leaves START..END-1 of a family: each by one certificate on its own path, or by a split set
    whose suffixes form a complete prefix code below it."""
    lawf, pricef, trf, fi, leavesf, s, e, certf, outf = argv[:9]
    bump = Q(argv[9]) if len(argv) > 9 else Q(0)                 # control (b) only: subtract `bump` nats
    t0 = time.process_time()
    law = json.load(open(lawf)); price = json.load(open(pricef)); tr = json.load(open(trf))
    C = Checker(law, price, tr)
    fi = int(fi); s = int(s); e = int(e)
    fam = families(N)[fi]
    stored = load_slice(leavesf, s, e)                         # stored[idx - s] is stored leaf idx
    res = dict(family=fi, name=fam[0], start=s, end=e, certs=os.path.basename(certf), leaves=e - s, accepted=0,
               rejected=[], split_leaves=[], vacuous=0, preassigned_steps=0, min_margin=None, min_path=None,
               nodes_checked=0, bump=str(bump))
    raw = gzip.open(certf, 'rb').read()
    res['certs_sha256'] = hashlib.sha256(raw).hexdigest()
    groups = {}
    for line in raw.decode().splitlines():
        if line.strip():
            c = json.loads(line); groups.setdefault(c['idx'], []).append(c)
    assert set(groups) == set(range(s, e)), 'certificate indices differ from the job range'
    for idx in range(s, e):
        sp = [list(q) for q in stored[idx - s]]
        cs = groups[idx]
        if len(cs) == 1 and cs[0]['path'] == sp:
            pass
        else:
            ok = all(c['path'][:len(sp)] == sp and len(c['path']) > len(sp) for c in cs)
            try:
                kraft([c['path'][len(sp):] for c in cs]) if ok else None
            except AssertionError:
                ok = False
            if not ok:
                res['rejected'].append(dict(idx=idx, path=sp, reason='certificate paths do not tile the stored leaf'))
                continue
            res['split_leaves'].append(dict(idx=idx, path=sp, children=len(cs)))
        good = True
        for c in cs:
            res['nodes_checked'] += 1
            acc, margin, why = check_node(C, fam, c, res)
            if margin is not None:
                margin -= bump
                acc = margin > 0
                if res['min_margin'] is None or margin < Q(res['min_margin']):
                    res['min_margin'] = str(margin); res['min_margin_float'] = float(margin); res['min_path'] = c['path']
            if not acc:
                good = False
                res['rejected'].append(dict(idx=idx, path=c['path'], reason=why,
                                            margin=None if margin is None else str(margin),
                                            margin_float=None if margin is None else float(margin)))
        if good:
            res['accepted'] += 1
    res['cpu_seconds'] = time.process_time() - t0
    res['independence'] = independence_assertion()
    tmp = outf + '.tmp'
    with open(tmp, 'w', newline='\n') as f:
        json.dump(res, f)
    os.replace(tmp, outf)
    print(json.dumps({k: v for k, v in res.items() if k not in ('rejected', 'min_path', 'split_leaves')}))
    print(res['independence'])


def check_kraft(argv):
    fi, leavesf, outf = argv
    t0 = time.process_time()
    fam = families(N)[int(fi)]
    raw = gzip.open(leavesf, 'rb').read()
    paths = json.loads(raw)
    maxlen = kraft(paths)
    res = dict(family=int(fi), name=fam[0], leaves=len(paths), max_depth=maxlen, kraft='complete prefix code, sum 1',
               leaves_sha256=hashlib.sha256(raw).hexdigest(), cpu_seconds=time.process_time() - t0)
    res['independence'] = independence_assertion()
    with open(outf, 'w', newline='\n') as f:
        json.dump(res, f)
    print(json.dumps(res))


def block(argv):
    """outward enclosure of one block's residual: on the grid (window of the exact grid mass) and on the true law
    (grid enclosure -/+ E_block, every Delta-widened window)."""
    lawf, pricef, trf, cells = argv
    law = json.load(open(lawf)); price = json.load(open(pricef)); tr = json.load(open(trf))
    C = Checker(law, price, tr)
    U = sorted({int(z) for z in cells.split(',')})
    r = [0] * N; c = [0] * N; m = 0; g = Q(0)
    for z in U:
        r[C.ROW[z]] += C.P[z]; c[C.COL[z]] += C.P[z]; m += C.P[z]; g += C.gq[z]
    hs = [C.grid.h(v) for v in r + c]; hm = C.grid.h(m)
    cost_lo = 2 * sum(a for a, _ in hs) - hm[1]; cost_hi = 2 * sum(b for _, b in hs) - hm[0]
    D = 1 << C.DL; U2 = price['U2']
    j = next(t for t in range(C.nwin) if price['lo'][t] * D < m * U2 <= price['hi'][t] * D)
    phi = C.phi_q[j]
    lo = Q(cost_lo, ONE) - g - phi; hi = Q(cost_hi, ONE) - g - phi
    wins = [t for t, _, _ in C.windows(m, m)]
    tlo = Q(cost_lo, ONE) - g - max(C.phi_q[t] for t in wins) - C.error
    thi = Q(cost_hi, ONE) - g - min(C.phi_q[t] for t in wins) + C.error
    out = dict(cells=len(U), grid_mass=m, grid_mass_float=m / D, window=j, grid_residual_lo=float(lo), grid_residual_hi=float(hi),
               grid_residual_lo_exact=str(lo), grid_residual_hi_exact=str(hi), widened_windows=wins,
               true_residual_lo=float(tlo), true_residual_hi=float(thi), true_negative=thi < 0, true_positive=tlo > 0)
    out['independence'] = independence_assertion()
    print(json.dumps(out))


def consts(argv):
    lawf, pricef, trf = argv
    law = json.load(open(lawf)); price = json.load(open(pricef)); tr = json.load(open(trf))
    C = Checker(law, price, tr)
    E = C.eblock_upper()
    out = dict(eblock_own_upper=str(E), eblock_own_float=float(E), stored_error=float(C.error),
               stored_ge_own=C.error >= E, delta=float(C.delta), phi0=str(C.phi_q[0]),
               phi_max=float(max(C.phi_q)), gamma15=float(C.gq[15]), grid_total=sum(C.P),
               p_symmetric=all(law['p_int'][d] == law['p_int'][(N - d) % N] for d in range(N)))
    assert out['stored_ge_own']
    out['independence'] = independence_assertion()
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    set_below_normal()
    mode = sys.argv[1]
    {'chunk': check_chunk, 'kraft': check_kraft, 'consts': consts, 'block': block}[mode](sys.argv[2:])
