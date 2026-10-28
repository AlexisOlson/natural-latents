"""Step 2: the exact cover at a frozen price, resumable per root family.

Search (float64, PACK-BOUND's repaired engine = pb/repaired_search.py's node loop, mass branching):
  * logical propagation (run/gap clauses of the family) uses only the logical on/off state;
  * the node bound omits free exact grid-zero cells (d = 15 orbit; requires gamma_15 <= 0), PROOF.txt section 4/8;
  * bound = Wolfe min-norm point on the penalized knapsack curve (pen.wmnp2p); leaf when bound >= 1e-7.
Exact check, inline, for every leaf (integer-only arithmetic: rf/fastcoef.py's coefficients, rf/fastlog.py's
table-reduced log and rf/fastenv.py's fixed-point envelope, each validated against pb/fast_integer_node_engine;
RF_ORIG_COEF=1 / RF_ORIG_ENV=1 switch back to pb's coefficients / envelope):
  * the node is rebuilt from the root and the branch path with an independent clause propagator;
  * the leaf's greedy orders and integer simplex weights are re-evaluated with outward entropy bounds, the
    fractional-knapsack/tangent envelope is taken over every window widened by Delta (grid-to-true mass error), and
    the block-cost transfer E_block is subtracted: accepted iff the result is > 0;
  * a weak proposal is retried with a longer min-norm run before the leaf is split further;
  * vacuous leaves are re-derived vacuous by the independent propagator; the leaf set is checked to be a complete
    binary prefix code (Kraft sum 1, consistent branch variables).
A family file is written only when the family is complete and every leaf passed. A violated block aborts.
usage: python3.13 cover.py PRICE.json OUTDIR [--procs=3] [--families=i,j|all] [--order=hard]"""
import sys, os, json, time, gzip, math, pickle
from common import *
from fractions import Fraction as Q

WD = 1 << 40
MARGIN = 1e-7


def transfer_bound():
    f = OUT / 'state' / 'transfer.json'
    if f.exists():
        d = json.loads(f.read_text()); return Q(d['delta']), Q(d['error'])
    from fast_integer_family import transfer
    L = load_law(); n = L['n']; den = L['den']
    P = [int(x) for x in L['pint']]
    delta, error, law = transfer(n, den, P)
    f.write_text(json.dumps(dict(delta=str(delta), error=str(error), delta_float=float(delta), error_float=float(error), law=law)))
    return delta, error


def clause_root(name, n):
    from fast_integer_family import root
    return root(name, n)


def logical_node(name, path, n):
    """independent re-derivation of a node: root + path, run/gap clause propagation, no zero omission."""
    from fast_integer_family import propagate
    on, off, clauses = clause_root(name, n)
    vac, on, off = propagate(on, off, clauses)
    for z, bit in path:
        assert not vac and z not in on | off and bit in (0, 1)
        (on if bit else off).add(z); vac, on, off = propagate(on, off, clauses)
    return vac, on, off


def kraft(paths):
    leafset = set(); branches = {}; children = {}; tot = Q()
    for path in paths:
        path = tuple(map(tuple, path)); assert path not in leafset; leafset.add(path); tot += Q(1, 1 << len(path))
        prefix = ()
        for z, bit in path:
            if prefix in branches: assert branches[prefix] == z
            else: branches[prefix] = z
            children.setdefault(prefix, set()).add(bit); prefix = prefix + ((z, bit),)
    assert tot == 1 and not leafset.intersection(branches) and all(v == {0, 1} for v in children.values())


class Exact:
    def __init__(self, price):
        from fast_integer_node_engine import coefficients, envelope
        self.coefficients = coefficients; self.envelope = envelope
        L = load_law(); n = L['n']; self.n = n; self.den = L['den']; self.P = [int(x) for x in L['pint']]
        self.gamma = [Q.from_float(price['gamma'][int(L['DIST'][z])]) for z in range(n * n)]
        assert all(self.gamma[z] <= 0 for z in range(n * n) if self.P[z] == 0)
        self.we = [Q(0)] + [Q(b, price['U2']) for b in price['hi']]; self.phi = [Q.from_float(v) for v in price['phi']]
        assert price['lo'][0] == 0 and price['lo'][1:] == price['hi'][:-1] and price['hi'][-1] == price['U2']
        self.delta, self.error = transfer_bound()
        if os.environ.get('RF_ORIG_LOG') != '1':
            import fastlog; fastlog.install()
        if os.environ.get('RF_ORIG_COEF') != '1':
            import fastcoef; self.coefficients = fastcoef.coefficients
        from fastenv import Env
        self.env = Env(self.den, self.we, self.phi, self.delta, price['U2'], coarse=os.environ.get('RF_PRECISE_ENV') != '1', Eblock=self.error)
        self.orig_env = os.environ.get('RF_ORIG_ENV') == '1'

    def check(self, on, off, orders, weights):
        fz, xlo, m0, base = self.coefficients(self.n, self.den, self.P, self.gamma, on, off, orders, weights, WD)
        if self.orig_env:
            value, info = self.envelope([self.P[z] for z in fz], xlo, self.den, m0, base, self.we, self.phi, error=self.delta)
        else:
            value = self.env.envelope([self.P[z] for z in fz], xlo, m0, base)
        return value - self.error


def proposal(O, lam):
    keep = [j for j in range(len(lam)) if lam[j] > 0]
    lam = np.array([lam[j] for j in keep]); O = [O[j] for j in keep]
    w = [max(0, int(math.floor(float(v) * WD))) for v in lam]; w[int(np.argmax(lam))] += WD - sum(w)
    return [list(map(int, o)) for o in O], w


def run_family(args):
    (i, price_file, od, tcap) = args
    nocheck = os.environ.get('RF_NOCHECK') == '1'          # experiments only: never used for a certificate
    branch = os.environ.get('RF_BRANCH', 'mass')
    QUICK = int(os.environ.get('RF_QUICK', 60)); DEEP = int(os.environ.get('RF_DEEP', 350)); DTOL = float(os.environ.get('RF_DTOL', 0.002))
    MK1 = int(os.environ.get('RF_MK1', 180)); MK2 = int(os.environ.get('RF_MK2', 250))
    from pen import wmnp2p, knap_pen, G_pen
    from core import node_setup
    from roots import roots_for_gap, propagate2
    price = json.loads(open(price_file).read()); L = load_law(); n = L['n']; P = L['P']; ROW = L['ROW']; COL = L['COL']
    gam = np.array(price['gamma'])[L['DIST']].astype(float); lo, hi, U2, we = load_windows(price); wv = np.array(price['phi'], float)
    spec = roots_for_gap(n)[i]; name = spec[0]
    ex = Exact(price)
    zero = P == 0
    on = np.zeros(n * n, bool); off = on.copy(); on[spec[1]] = True; off[spec[2]] = True
    stack = [(on, off, None, ())]; nodes = 0; leaves = []; t0 = time.time(); minleaf = 1e300; minexact = None
    nvac = 0; nretry = 0; nsplit = 0; viol = None; tcheck = 0.0; before = 0.0; cbefore = 0.0
    psha = sha(price_file); stf = os.path.join(od, f'state_{i}.json.gz')
    if os.path.exists(stf) and not nocheck:          # resume a checkpointed family (same price only)
        S = json.load(gzip.open(stf, 'rt')); assert S['price_sha256'] == psha and S['i'] == i
        nodes = S['nodes']; leaves = [tuple(map(tuple, p)) for p in S['leaves']]; nvac = S['vacuous']; nretry = S['retries']
        nsplit = S['splits']; minleaf = S['minleaf']; minexact = Q(S['minexact']) if S['minexact'] else None
        before = S['seconds']; cbefore = S['check_seconds']; stack = []
        for it in S['stack']:
            a = np.zeros(n * n, bool); b = a.copy(); a[it[0]] = True; b[it[1]] = True
            stack.append((a, b, None if it[2] is None else np.array(it[2], np.int64), tuple(map(tuple, it[3]))))

    def persist():
        S = dict(i=i, name=name, price_sha256=psha, nodes=nodes, leaves=[list(map(list, p)) for p in leaves], vacuous=nvac,
                 retries=nretry, splits=nsplit, minleaf=minleaf, minexact=str(minexact) if minexact is not None else None,
                 seconds=before + time.time() - t0, check_seconds=cbefore + tcheck,
                 stack=[(np.nonzero(a)[0].tolist(), np.nonzero(b)[0].tolist(), None if c is None else c.tolist(), list(map(list, pth)))
                        for a, b, c, pth in stack],
                 covered_mass=float(sum(Q(1, 1 << len(p)) for p in leaves)))
        tmp = stf + '.tmp'
        with gzip.open(tmp, 'wt') as f: json.dump(S, f)
        os.replace(tmp, stf)
    lastp = time.time()
    while stack:
        if tcap and time.time() - t0 > tcap:
            break
        if not nocheck and time.time() - lastp > 600:
            persist(); lastp = time.time()
        on, off, initial, path = stack.pop(); nodes += 1
        vac, on, off = propagate2(on, off, spec[3], spec[4], spec[5])
        if vac:
            ts = time.time(); v2, _, _ = logical_node(name, path, n); assert v2, (name, path); tcheck += time.time() - ts
            leaves.append(path); nvac += 1; continue
        offb = off | (zero & ~on)
        fz, p, ri, ci, gf, r0, c0, m0, base = node_setup(on, offb, P, ROW, COL, gam, n)
        k = len(p)
        if k == 0:
            g = G_pen(on, P, ROW, COL, gam, n, we, wv, True)
            if g < MARGIN:
                viol = dict(value=float(g), cells=np.nonzero(on)[0].tolist(), path=list(path)); break
            O, lam = [[]], [1.0]; lb = g
        else:
            if initial is None: order = np.argsort(gf / p).astype(np.int64)
            else:
                rank = np.full(n * n, n * n, dtype=np.int64); rank[initial] = np.arange(len(initial)); order = np.argsort(rank[fz]).astype(np.int64)
            lb, x, O, lam, status, wit = wmnp2p(k, p, ri, ci, r0, c0, gf, m0, base, MARGIN, QUICK, order, min(MK1, k + 2), n, 0, we, wv)
            if lb < MARGIN and lb > -DTOL and status == 0:
                r2 = wmnp2p(k, p, ri, ci, r0, c0, gf, m0, base, MARGIN, DEEP, np.argsort(x / p).astype(np.int64), min(MK2, k + 2), n, 0, we, wv)
                if r2[0] > lb: lb, x, O, lam = r2[0], r2[1], r2[2], r2[3]
        if nodes % 2000 == 0 and os.environ.get('RF_VERBOSE') == '1':
            print(f'  {name}: nodes {nodes} leaves {len(leaves)} stack {len(stack)} depth {len(path)} t {time.time()-t0:.0f}', flush=True)
        if lb >= MARGIN and nocheck:
            leaves.append(path); minleaf = min(minleaf, float(lb)); continue
        if lb >= MARGIN:
            ts = time.time()
            vac2, son, soff = logical_node(name, path, n); assert not vac2
            assert son == set(np.nonzero(on)[0].tolist()) and soff == set(np.nonzero(off)[0].tolist()), (name, path)
            Oi, w = proposal(O, lam)
            val = ex.check(son, soff, Oi, w)
            if val <= 0 and k:
                nretry += 1
                r3 = wmnp2p(k, p, ri, ci, r0, c0, gf, m0, base, 1e300, 2000, np.argsort(x / p).astype(np.int64), min(400, k + 2), n, 0, we, wv)
                Oi, w = proposal(r3[2], r3[3]); val = ex.check(son, soff, Oi, w)
            tcheck += time.time() - ts
            if val > 0:
                leaves.append(path); minleaf = min(minleaf, float(lb))
                if minexact is None or val < minexact: minexact = val
                continue
            nsplit += 1          # exact check too weak: split this node further
            if k == 0:
                viol = dict(value=float(lb), cells=np.nonzero(on)[0].tolist(), path=list(path), exact=str(val)); break
        if k == 0:
            continue
        kb, mu, bidx = knap_pen(x, p, m0, we, wv); order = np.argsort(x / p); j = int(np.searchsorted(np.cumsum(p[order]), mu))
        for count in (j, j + 1):
            witness = on.copy(); witness[fz[order[:count]]] = True
            value = G_pen(witness, P, ROW, COL, gam, n, we, wv, True)
            if value < -1e-12:
                viol = dict(value=float(value), cells=np.nonzero(witness)[0].tolist(), path=list(path)); break
        if viol: break
        e = int(np.argmax(p))
        if branch == 'frac' and bidx >= 0:
            e = int(bidx)
        if branch == 'line':
            lf = np.nonzero(np.isin(fz, spec[3]))[0]
            if len(lf): e = int(lf[np.argmax(p[lf])])
        z = int(fz[e]); a = on.copy(); a[z] = True; b = off.copy(); b[z] = True; initial = fz[order]
        stack.append((on, b, initial, path + ((z, 0),))); stack.append((a, off, initial, path + ((z, 1),)))
    secs = before + time.time() - t0; tcheck += cbefore
    complete = (not stack) and viol is None
    if stack and viol is None and not nocheck:
        persist()
    if complete:
        kraft(leaves)
    if nocheck:
        complete = False      # never written as a family certificate
    res = dict(i=i, name=name, nodes=nodes, leaves=len(leaves), vacuous=nvac, seconds=secs, check_seconds=tcheck,
               complete=complete, violation=viol, float_min_leaf=minleaf if minleaf < 1e299 else None,
               exact_min=str(minexact) if minexact is not None else None,
               exact_min_float=float(minexact) if minexact is not None else None, retries=nretry, splits=nsplit,
               stack=len(stack), price_sha256=sha(price_file), nocheck=nocheck, branch=branch)
    if complete:
        with gzip.open(os.path.join(od, f'leaves_{i}.json.gz'), 'wt') as f:
            json.dump([[list(s) for s in pth] for pth in leaves], f)
        tmp = os.path.join(od, f'fam_{i}.json.tmp'); open(tmp, 'w').write(json.dumps(res)); os.replace(tmp, os.path.join(od, f'fam_{i}.json'))
        if os.path.exists(stf): os.remove(stf)
    else:
        res['covered_mass'] = float(sum(Q(1, 1 << len(p)) for p in leaves))
    return res


def main():
    pf, od = sys.argv[1], sys.argv[2]
    opt = dict(a.split('=', 1) for a in sys.argv[3:] if '=' in a)
    os.makedirs(od, exist_ok=True)
    from roots import roots_for_gap
    roots = roots_for_gap(30)
    fam = opt.get('--families', 'all')
    idx = list(range(len(roots))) if fam == 'all' else [int(x) for x in fam.split(',')]
    if opt.get('--order', 'hard') == 'hard':
        dd = {i: int(roots[i][0].split('_')[0][1:]) for i in idx}
        idx.sort(key=lambda i: (dd[i], i))
    tcap = float(opt['--tcap']) if '--tcap' in opt else None
    todo = [i for i in idx if not os.path.exists(os.path.join(od, f'fam_{i}.json'))]
    transfer_bound()
    print(f'{len(todo)} of {len(idx)} families to run; price {pf} sha {sha(pf)}', flush=True)
    logf = open(os.path.join(od, 'cover.log'), 'a')
    from multiprocessing import Pool
    procs = int(opt.get('--procs', 3))
    with Pool(procs) as pool:
        for res in pool.imap_unordered(run_family, [(i, pf, od, tcap) for i in todo]):
            line = json.dumps({k: v for k, v in res.items() if k not in ('exact_min',)})
            print(line, flush=True); logf.write(line + '\n'); logf.flush()
            if res['violation'] is not None:
                json.dump(res, open(os.path.join(od, f'VIOLATION_{res["i"]}.json'), 'w'))
                if opt.get('--stop', '1') == '1':
                    print('VIOLATION: stopping', flush=True); pool.terminate(); return 2
    return 0


if __name__ == '__main__':
    sys.exit(main())
