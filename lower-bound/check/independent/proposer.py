"""PACK-REPLAY-V4 proposer (UNTRUSTED; its output gets no credit).

Regenerates one greedy-order certificate per stored leaf by re-running PACK-REFREEZE's own search (rf/cover.py's
node loop: propagate2, node_setup, pen.wmnp2p with the parent's order as warm start, proposal()). It walks the stored
tree from the root, so every node gets the same warm start the engine gave it. Run from a byte copy of
PACK-REFREEZE/out/rf (sys.path is set by rf/common.py).

usage: python proposer.py REFREEZE_RF_DIR PRICE.json LEAVES.json.gz FAMILY START END OUT.jsonl.gz [--deep] [--split=D]
  --deep     certify each leaf with the engine's retry run (2000 iterations, up to 400 orders) instead of QUICK/DEEP
  --split=D  instead of certifying the leaf, split it D more levels (largest-mass free cell) and certify the children
"""
import sys, os, json, gzip, time, math


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


def main():
    rfdir, pricef, leavesf, fi, s, e, outf = sys.argv[1:8]
    opts = dict(a.split('=', 1) if '=' in a else (a, '1') for a in sys.argv[8:])
    deep = '--deep' in opts; split = int(opts.get('--split', 0))
    if os.name == 'nt':
        import ctypes
        k32 = ctypes.windll.kernel32; k32.GetCurrentProcess.restype = ctypes.c_void_p
        k32.SetPriorityClass.argtypes = [ctypes.c_void_p, ctypes.c_uint32]; k32.SetPriorityClass(k32.GetCurrentProcess(), 0x4000)
    os.chdir(rfdir); sys.path.insert(0, rfdir)
    from common import np, load_law, load_windows
    from pen import wmnp2p
    from core import node_setup
    from roots import roots_for_gap, propagate2
    from cover import proposal, WD, MARGIN
    QUICK, DEEP, DTOL, MK1, MK2 = 60, 350, 0.002, 180, 250
    fi = int(fi); s = int(s); e = int(e)
    price = json.load(open(pricef)); L = load_law(); n = L['n']; P = L['P']; ROW = L['ROW']; COL = L['COL']
    gam = np.array(price['gamma'])[L['DIST']].astype(float); lo, hi, U2, we = load_windows(price); wv = np.array(price['phi'], float)
    zero = P == 0
    spec = roots_for_gap(n)[fi]
    paths = load_slice(leavesf, s, e)                              # paths[t - s] is stored leaf t
    job = {tuple(map(tuple, paths[t - s])): t for t in range(s, e)}
    branch = {}; inner = set()
    for pth in job:
        for d in range(len(pth)):
            pre = pth[:d]; inner.add(pre)
            assert branch.setdefault(pre, pth[d][0]) == pth[d][0]
    t0 = time.process_time(); out = []; stats = dict(nodes=0, anomalies=[], inline_retries=0)

    def bound(on, off, initial, deepmode):
        offb = off | (zero & ~on)
        fz, p, ri, ci, gf, r0, c0, m0, base = node_setup(on, offb, P, ROW, COL, gam, n)
        k = len(p)
        if k == 0:
            return fz, p, 0, None, [[]], [1.0]
        if initial is None:
            order = np.argsort(gf / p).astype(np.int64)
        else:
            rank = np.full(n * n, n * n, dtype=np.int64); rank[initial] = np.arange(len(initial)); order = np.argsort(rank[fz]).astype(np.int64)
        lb, x, O, lam, status, wit = wmnp2p(k, p, ri, ci, r0, c0, gf, m0, base, MARGIN, QUICK, order, min(MK1, k + 2), n, 0, we, wv)
        if lb < MARGIN and lb > -DTOL and status == 0:
            r2 = wmnp2p(k, p, ri, ci, r0, c0, gf, m0, base, MARGIN, DEEP, np.argsort(x / p).astype(np.int64), min(MK2, k + 2), n, 0, we, wv)
            if r2[0] > lb: lb, x, O, lam = r2[0], r2[1], r2[2], r2[3]
        if deepmode or (deepmode is None and lb < MARGIN):
            # the engine's own retry (cover.py:177); deepmode None = only when the float bound is weak (inline retry)
            r3 = wmnp2p(k, p, ri, ci, r0, c0, gf, m0, base, 1e300, 2000, np.argsort(x / p).astype(np.int64), min(400, k + 2), n, 0, we, wv)
            if deepmode or r3[0] > lb:
                lb, x, O, lam = r3[0], r3[1], r3[2], r3[3]
            stats['inline_retries'] += deepmode is None
        return fz, p, lb, x, O, lam

    def emit(idx, pth, on, off, initial, deepmode):
        vac, on, off = propagate2(on, off, spec[3], spec[4], spec[5])
        if vac:
            out.append(dict(idx=idx, path=[list(q) for q in pth], vacuous=True)); return
        fz, p, lb, x, O, lam = bound(on, off, initial, deepmode)
        Oi, w = proposal(O, lam) if len(p) else ([[]], [WD])
        if len(p) == 0:
            Oi, w = [], []
        out.append(dict(idx=idx, path=[list(q) for q in pth], vacuous=False, on=np.nonzero(on)[0].tolist(),
                        fz=[int(z) for z in fz], orders=Oi, weights=w, lb=float(lb)))

    def split_emit(idx, pth, on, off, initial, depth):
        """certify the children of a leaf down to `depth` more levels (engine's mass branching)."""
        vac, on, off = propagate2(on, off, spec[3], spec[4], spec[5])
        if vac:
            out.append(dict(idx=idx, path=[list(q) for q in pth], vacuous=True)); return
        if depth == 0:
            return emit(idx, pth, on, off, initial, True)
        fz, p, lb, x, O, lam = bound(on, off, initial, True)
        if len(p) == 0:
            return emit(idx, pth, on, off, initial, True)
        ini = fz[np.argsort(x / p)]; z = int(fz[int(np.argmax(p))])
        a = on.copy(); a[z] = True; b = off.copy(); b[z] = True
        split_emit(idx, pth + ((z, 1),), a, off, ini, depth - 1)
        split_emit(idx, pth + ((z, 0),), on, b, ini, depth - 1)

    on = np.zeros(n * n, bool); off = on.copy(); on[spec[1]] = True; off[spec[2]] = True
    stack = [(on, off, None, ())]
    while stack:
        on, off, initial, pre = stack.pop(); stats['nodes'] += 1
        if pre in job:
            if split:
                split_emit(job[pre], pre, on, off, initial, split)
            else:
                emit(job[pre], pre, on, off, initial, True if deep else None)
            continue
        assert pre in inner
        vac, on, off = propagate2(on, off, spec[3], spec[4], spec[5])
        if vac:
            stats['anomalies'].append(dict(kind='vacuous internal node', path=[list(q) for q in pre])); continue
        fz, p, lb, x, O, lam = bound(on, off, initial, False)
        z = branch[pre]
        if len(p) == 0 or z not in set(fz.tolist()):
            stats['anomalies'].append(dict(kind='branch cell not free', path=[list(q) for q in pre], z=z)); continue
        ini = fz[np.argsort(x / p)]
        a = on.copy(); a[z] = True; b = off.copy(); b[z] = True
        for child in ((pre + ((z, 0),), on, b), (pre + ((z, 1),), a, off)):
            if child[0] in inner or child[0] in job:
                stack.append((child[1], child[2], ini, child[0]))
    tmp = outf + '.tmp'
    with gzip.open(tmp, 'wt', compresslevel=3, newline='\n') as f:
        for c in sorted(out, key=lambda c: (c['idx'], c['path'])):
            f.write(json.dumps(c, separators=(',', ':')) + '\n')
    os.replace(tmp, outf)
    stats.update(family=fi, start=s, end=e, certs=len(out), cpu_seconds=time.process_time() - t0, deep=deep, split=split)
    with open(outf + '.stats.json', 'w', newline='\n') as f:
        json.dump(stats, f)
    print(json.dumps(stats), flush=True)


if __name__ == '__main__':
    main()
