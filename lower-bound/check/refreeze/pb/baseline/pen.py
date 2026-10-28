"""Penalized separation oracle (search phase, float64).

Residual of a block U = A + W (A forced on, W within the free set W0):
    G(U) = c(U) - gamma(U) - phi(p(U)),   phi a step function of block mass.
Windows: edges e_0 = 0 < e_1 < ... < e_K, window j = (e_j, e_{j+1}], value phi_j; masses beyond e_K get phi = 0
is NOT assumed: callers must pass e_K >= the largest attainable mass.

Node bound (the record's bound, core.py docstring, with the 1-d step taken per window):
    G(U) >= F0 - g0 + sigma_x(mu) + psi(M) - phi(M),   M = m(A) + mu, mu = m(W),
and sigma_x(mu) + psi(M) is convex on each knapsack segment. On (segment) x (closure of window j) the minimum of the
convex part is attained at the clamp of exp(-1 - rho); subtracting phi_j there is a valid lower bound on that piece
(the closure only enlarges the set minimised over). The node bound is the minimum over all pieces.
x is the Wolfe min-norm point (core2.wmnp2's iteration, unchanged): its knapsack curve is the convex envelope of
mu -> min{S(W) : m(W) = mu} at every mu at once, so one x serves all windows and window branching adds nothing over
cell branching.
"""
import time
import numpy as np
from numba import njit
from core import hf, greedy, node_setup
from core2 import chol_add, chol_del, chol_solve_ones, S_of
from roots import propagate, propagate2


@njit(cache=False)
def phi_of(M, we, wv):
    """phi(M) for window j = (e_j, e_{j+1}]."""
    K = wv.shape[0]
    j = np.searchsorted(we, M, side='left') - 1
    if j < 0:
        j = 0
    if j >= K:
        j = K - 1
    return wv[j]


@njit(cache=False)
def phi_max(M, we, wv, tol=1e-12):
    """max of phi over the windows whose tol-widened closure contains M (search-phase lower bounds)."""
    K = wv.shape[0]
    v = -1e300
    for j in range(K):
        if we[j] - tol <= M and M <= we[j + 1] + tol:
            if wv[j] > v:
                v = wv[j]
    return v


@njit(cache=False)
def knap_pen(x, p, m0, we, wv):
    """min over mu in [0, m(W0)] of sigma_x(mu) + psi(m0 + mu) - phi(m0 + mu).
    Returns (value, argmin mu, index of knapsack cell holding the argmin or -1)."""
    k = x.shape[0]
    rat = x / p
    order = np.argsort(rat)
    K = wv.shape[0]
    best = 1e300; bmu = 0.0; bidx = -1
    if m0 > 0:
        best = m0 * np.log(m0) - phi_max(m0, we, wv)
    mu = 0.0; s = 0.0
    tol = 1e-12        # every window piece is widened by tol: masses on an edge get the larger of the two phis
    j = 0
    for jj in range(k):
        e = order[jj]
        rho = rat[e]
        a = m0 + mu; b = m0 + mu + p[e]
        while j > 0 and we[j] + tol >= a:
            j -= 1
        while j < K - 1 and we[j + 1] + tol < a:
            j += 1
        jw = j
        while jw < K and we[jw] - tol <= b:
            lo = a if a > we[jw] - tol else we[jw] - tol
            hi = b if b < we[jw + 1] + tol else we[jw + 1] + tol
            if hi >= lo:
                M = np.exp(-1.0 - rho)
                if M < lo:
                    M = lo
                if M > hi:
                    M = hi
                if M > 0:
                    val = s + rho * (M - a) + M * np.log(M) - wv[jw]
                    if val < best:
                        best = val; bmu = M - m0; bidx = e
            jw += 1
        mu += p[e]; s += x[e]
    return best, bmu, bidx


@njit(cache=False)
def wmnp2p(k, p, ri, ci, r0, c0, gfree, m0, base, target, maxit, init_order, maxk, n, witness_every, we, wv):
    """core2.wmnp2 with knap_bound replaced by knap_pen (bound includes -phi)."""
    V = np.zeros((maxk, k)); O = np.zeros((maxk, k), dtype=np.int64)
    L = np.zeros((maxk, maxk)); lam = np.zeros(maxk)
    ip = 1.0 / p
    q = np.zeros(k)
    greedy(init_order, k, p, ri, ci, r0, c0, gfree, q)
    g00 = np.sum(q * q * ip)
    eps = 1e-12 * g00 + 1e-300
    V[0] = q; O[0] = init_order; L[0, 0] = np.sqrt(g00 + eps); lam[0] = 1.0; cnt = 1
    x = q.copy()
    best = -1e300; bestx = x.copy(); bestO = O[:1].copy(); bestlam = lam[:1].copy()
    wit = 1e300
    status = 0
    sel = np.zeros(k, dtype=np.bool_)
    for it in range(maxit):
        kb, mu, bidx = knap_pen(x, p, m0, we, wv)
        val = base + kb
        if val > best:
            best = val; bestx = x.copy(); bestO = O[:cnt].copy(); bestlam = lam[:cnt].copy()
        if best >= target:
            status = 1
            break
        if witness_every > 0 and it % witness_every == 0:
            order = np.argsort(x * ip)
            sel[:] = False
            acc = 0.0
            for jj in range(k):
                if acc >= mu - 1e-15:
                    break
                sel[order[jj]] = True; acc += p[order[jj]]
            Sw, mw = S_of(sel, k, p, ri, ci, r0, c0, gfree, n)
            M = m0 + mw
            gw = base + Sw + M * np.log(M) - phi_of(M, we, wv)
            if gw < wit:
                wit = gw
            if wit < target:
                status = 2
                break
        order = np.argsort(x * ip)
        greedy(order, k, p, ri, ci, r0, c0, gfree, q)
        xx = np.sum(x * x * ip); xq = np.sum(x * q * ip)
        if xx - xq <= 1e-12 * max(xx, 1e-30):
            status = 3
            break
        if cnt >= maxk:
            break
        gvec = np.zeros(cnt)
        for j in range(cnt):
            gvec[j] = np.sum(V[j] * q * ip)
        if not chol_add(L, cnt, gvec, np.sum(q * q * ip) + eps):
            status = 3
            break
        V[cnt] = q; O[cnt] = order; lam[cnt] = 0.0
        cnt += 1
        for minor in range(maxk + 1):
            z = chol_solve_ones(L, cnt)
            alpha = z / z.sum()
            ok = True
            for j in range(cnt):
                if alpha[j] <= 1e-15:
                    ok = False
            if ok:
                for j in range(cnt):
                    lam[j] = alpha[j]
                break
            theta = 1.0; jdel = -1
            for j in range(cnt):
                if alpha[j] <= 1e-15:
                    den = lam[j] - alpha[j]
                    if den > 0:
                        t = lam[j] / den
                        if t < theta:
                            theta = t; jdel = j
            for j in range(cnt):
                lam[j] = lam[j] + theta * (alpha[j] - lam[j])
            if jdel < 0:
                jdel = 0
                for j in range(cnt):
                    if lam[j] < lam[jdel]:
                        jdel = j
            chol_del(L, cnt, jdel)
            for j in range(jdel, cnt - 1):
                V[j] = V[j + 1]; O[j] = O[j + 1]; lam[j] = lam[j + 1]
            cnt -= 1
            s_ = 0.0
            for j in range(cnt):
                if lam[j] < 0:
                    lam[j] = 0.0
                s_ += lam[j]
            for j in range(cnt):
                lam[j] /= s_
            if cnt == 1:
                lam[0] = 1.0
                break
        x = np.zeros(k)
        for j in range(cnt):
            x += lam[j] * V[j]
    kb, mu, bidx = knap_pen(x, p, m0, we, wv)
    if base + kb > best:
        best = base + kb; bestx = x.copy(); bestO = O[:cnt].copy(); bestlam = lam[:cnt].copy()
    return best, bestx, bestO, bestlam, status, wit


@njit(cache=False)
def G_pen(x, P, ROW, COL, gam, n, we, wv, robust=False):
    r = np.zeros(n); c = np.zeros(n); m = 0.0; g = 0.0
    for z in range(x.shape[0]):
        if x[z]:
            r[ROW[z]] += P[z]; c[COL[z]] += P[z]; m += P[z]; g += gam[z]
    t = 0.0
    for i in range(n):
        t += 2 * hf(r[i]) + 2 * hf(c[i])
    if robust:
        return t - hf(m) - g - phi_max(m, we, wv)
    return t - hf(m) - g - phi_of(m, we, wv)


def node_bound(on, off, P, ROW, COL, gam, n, we, wv, maxit=3000, maxk=700):
    """Penalized lower bound over every U with on <= U <= ~off (U nonempty when on is nonempty)."""
    fz, p, ri, ci, gf, r0, c0, m0, base = node_setup(on, off, P, ROW, COL, gam, n)
    k = len(fz)
    if k == 0:
        return G_pen(on, P, ROW, COL, gam, n, we, wv, True)
    init = np.argsort(gf / p).astype(np.int64)
    lb, x, Oc, lam, st, wit = wmnp2p(k, p, ri, ci, r0, c0, gf, m0, base, 1e300, maxit, init, min(maxk, k + 2), n, 0,
                                     we, wv)
    return lb


def run_root_pen(spec, P, ROW, COL, gam, n, margin, we, wv, maxit=3000, maxk=700, node_cap=10 ** 7, quick=60,
                 deep_tol=2e-3, max_viol=1, record=True, wit_every=0, time_cap=None):
    """bnb.run_root for the penalized residual.  spec = (on cells, off cells, line, L, G) of one root family.
    Returns dict with nodes, leaves, violations [(G, cells)], complete flag."""
    N = P.shape[0]
    on = np.zeros(N, dtype=np.bool_); off = np.zeros(N, dtype=np.bool_)
    on[list(spec[0])] = True; off[list(spec[1])] = True
    stack = [(on, off, None, ())]
    nodes = 0; leaves = []; minlb = 1e9; viol = []
    t0 = time.time()
    while stack:
        on, off, init, path = stack.pop()
        nodes += 1
        vac, on, off = propagate2(on, off, spec[2], spec[3], spec[4])
        if vac:
            leaves.append(path)
            continue
        fz, p, ri, ci, gf, r0, c0, m0, base = node_setup(on, off, P, ROW, COL, gam, n)
        k = len(fz)
        if k == 0:
            g = G_pen(on, P, ROW, COL, gam, n, we, wv, True)
            if g < margin:
                viol.append((float(g), np.nonzero(on)[0].tolist()))
            else:
                leaves.append(path); minlb = min(minlb, g)
            continue
        if init is None:
            init = np.argsort(gf / p)
        else:
            rank = np.full(N, 10 ** 9, dtype=np.int64)
            rank[init] = np.arange(len(init))
            init = np.argsort(rank[fz], kind='stable').astype(np.int64)
        init = init.astype(np.int64)
        lb, x, Ocor, lam, status, wit = wmnp2p(k, p, ri, ci, r0, c0, gf, m0, base, margin, quick, init,
                                               min(maxk, k + 2), n, wit_every, we, wv)
        if lb < margin and lb > -deep_tol and status == 0:
            lb2, x2, Ocor2, lam2, status2, wit2 = wmnp2p(k, p, ri, ci, r0, c0, gf, m0, base, margin, maxit,
                                                         np.argsort(x / p).astype(np.int64), min(maxk, k + 2), n, 5,
                                                         we, wv)
            if lb2 > lb:
                lb, x = lb2, x2
        if lb >= margin:
            leaves.append(path); minlb = min(minlb, lb)
            continue
        kb, mu, bidx = knap_pen(x, p, m0, we, wv)
        order = np.argsort(x / p)
        cum = np.cumsum(p[order])
        j = int(np.searchsorted(cum, mu - 1e-15))
        wit = on.copy(); wit[fz[order[:j]]] = True
        # also try prefixes j-1, j+1 (window edges)
        for jj in (j, j + 1, j - 1):
            if 0 <= jj <= k:
                w2 = on.copy(); w2[fz[order[:jj]]] = True
                gw = G_pen(w2, P, ROW, COL, gam, n, we, wv)
                if gw < margin:
                    viol.append((float(gw), np.nonzero(w2)[0].tolist()))
                    break
        if sum(1 for v in viol if v[0] < 0) >= max_viol:
            return dict(nodes=nodes, leaves=len(leaves), minleaf=minlb, violations=viol, complete=False,
                        secs=time.time() - t0, leaf_paths=None, aborted=True)
        e = bidx if bidx >= 0 else int(np.argmax(p))
        z = int(fz[e])
        on2 = on.copy(); on2[z] = True
        off2 = off.copy(); off2[z] = True
        po = fz[np.argsort(x / p)]
        po = po[po != z].astype(np.int64)
        stack.append((on, off2, po, path + ((z, 0),)))
        stack.append((on2, off, po, path + ((z, 1),)))
        if nodes >= node_cap or (time_cap is not None and time.time() - t0 > time_cap):
            break
    neg = [v for v in viol if v[0] < 0]
    return dict(nodes=nodes, leaves=len(leaves), minleaf=minlb, violations=(neg if neg else viol[:5]),
                complete=(not stack), secs=time.time() - t0, leaf_paths=leaves if record else None,
                aborted=bool(neg))


def law_arrays(p):
    """Flatten an n x n law: P (n*n), ROW, COL, DIST (cell-distance orbit)."""
    n = p.shape[0]
    x = np.repeat(np.arange(n), n); y = np.tile(np.arange(n), n)
    k = (x - y) % n
    DIST = np.minimum(k, (n - k) % n)
    return p.ravel().astype(float).copy(), x.astype(np.int64), y.astype(np.int64), DIST.astype(np.int64)


# ---------------- window closure ("branch on windows") ----------------
# A node carries the set of windows still open. At a node the penalized bound is computed per window; every window
# whose bound reaches the margin is closed for the whole subtree (all blocks of the subtree with mass in that window
# are certified at this node). The node is a leaf when no window is open. Children bound only the open windows.

@njit(cache=False)
def knap_pen_w(x, p, m0, we, wv, active):
    """Per-window minima of sigma_x(mu) + psi(m0 + mu) - phi_w over mu in [0, m(W0)] with m0 + mu in the
    tol-widened closure of window w (1e300 when the window is unreachable). Also the active-window argmin
    (value, mu, knapsack cell index)."""
    k = x.shape[0]
    K = wv.shape[0]
    rat = x / p
    order = np.argsort(rat)
    bw = np.full(K, 1e300)
    best = 1e300; bmu = 0.0; bidx = -1
    tol = 1e-12
    if m0 > 0:
        for j in range(K):
            if we[j] - tol <= m0 and m0 <= we[j + 1] + tol:
                v = m0 * np.log(m0) - wv[j]
                if v < bw[j]:
                    bw[j] = v
                if active[j] and v < best:
                    best = v; bmu = 0.0; bidx = -1
    mu = 0.0; s = 0.0
    j = 0
    for jj in range(k):
        e = order[jj]
        rho = rat[e]
        a = m0 + mu; b = m0 + mu + p[e]
        while j > 0 and we[j] + tol >= a:
            j -= 1
        while j < K - 1 and we[j + 1] + tol < a:
            j += 1
        jw = j
        while jw < K and we[jw] - tol <= b:
            lo = a if a > we[jw] - tol else we[jw] - tol
            hi = b if b < we[jw + 1] + tol else we[jw + 1] + tol
            if hi >= lo:
                M = np.exp(-1.0 - rho)
                if M < lo:
                    M = lo
                if M > hi:
                    M = hi
                if M > 0:
                    val = s + rho * (M - a) + M * np.log(M) - wv[jw]
                    if val < bw[jw]:
                        bw[jw] = val
                    if active[jw] and val < best:
                        best = val; bmu = M - m0; bidx = e
            jw += 1
        mu += p[e]; s += x[e]
    return bw, best, bmu, bidx


def run_root_penw(spec, P, ROW, COL, gam, n, margin, we, wv, maxit=3000, maxk=700, node_cap=10 ** 7, quick=60,
                  deep_tol=2e-3, max_viol=1, record=True, time_cap=None):
    """run_root_pen with window closure. Records closures [(path, windows closed at that node)] and terminal leaves."""
    N = P.shape[0]; K = wv.shape[0]
    on = np.zeros(N, dtype=np.bool_); off = np.zeros(N, dtype=np.bool_)
    on[list(spec[0])] = True; off[list(spec[1])] = True
    stack = [(on, off, None, (), np.ones(K, dtype=np.bool_))]
    nodes = 0; leaves = []; closures = []; viol = []; minlb = 1e9
    t0 = time.time()
    while stack:
        on, off, init, path, act = stack.pop()
        nodes += 1
        vac, on, off = propagate2(on, off, spec[2], spec[3], spec[4])
        if vac:
            leaves.append(path)
            continue
        fz, p, ri, ci, gf, r0, c0, m0, base = node_setup(on, off, P, ROW, COL, gam, n)
        k = len(fz)
        if k == 0:
            g = G_pen(on, P, ROW, COL, gam, n, we, wv, True)
            if g < margin:
                viol.append((float(g), np.nonzero(on)[0].tolist()))
            else:
                leaves.append(path); minlb = min(minlb, g)
            continue
        if init is None:
            init = np.argsort(gf / p)
        else:
            rank = np.full(N, 10 ** 9, dtype=np.int64)
            rank[init] = np.arange(len(init))
            init = np.argsort(rank[fz], kind='stable').astype(np.int64)
        init = init.astype(np.int64)
        # the MNP iteration only needs the active-window bound to decide when to stop
        wvm = np.where(act, wv, -1e300)          # inactive windows never limit the bound
        lb, x, Ocor, lam, status, wit = wmnp2p(k, p, ri, ci, r0, c0, gf, m0, base, margin, quick, init,
                                               min(maxk, k + 2), n, 0, we, wvm)
        if lb < margin and lb > -deep_tol and status == 0:
            lb2, x2, _, _, _, _ = wmnp2p(k, p, ri, ci, r0, c0, gf, m0, base, margin, maxit,
                                         np.argsort(x / p).astype(np.int64), min(maxk, k + 2), n, 5, we, wvm)
            if lb2 > lb:
                lb, x = lb2, x2
        bw, best, mu, bidx = knap_pen_w(x, p, m0, we, wv, act)
        closed = act & (base + bw >= margin)
        if closed.any():
            closures.append((path, np.nonzero(closed)[0].astype(np.int16)))
        act2 = act & ~closed
        if not act2.any():
            leaves.append(path); minlb = min(minlb, float(np.min(base + bw[act])) if act.any() else 1e9)
            continue
        order = np.argsort(x / p)
        cum = np.cumsum(p[order])
        j = int(np.searchsorted(cum, mu - 1e-15))
        for jj in (j, j + 1, j - 1):
            if 0 <= jj <= k:
                w2 = on.copy(); w2[fz[order[:jj]]] = True
                gw = G_pen(w2, P, ROW, COL, gam, n, we, wv)
                if gw < margin:
                    viol.append((float(gw), np.nonzero(w2)[0].tolist()))
                    break
        if sum(1 for v in viol if v[0] < 0) >= max_viol:
            return dict(nodes=nodes, leaves=len(leaves), minleaf=minlb, violations=viol, complete=False,
                        secs=time.time() - t0, leaf_paths=None, closures=None, aborted=True)
        e = bidx if bidx >= 0 else int(np.argmax(p))
        z = int(fz[e])
        on2 = on.copy(); on2[z] = True
        off2 = off.copy(); off2[z] = True
        po = fz[np.argsort(x / p)]
        po = po[po != z].astype(np.int64)
        stack.append((on, off2, po, path + ((z, 0),), act2))
        stack.append((on2, off, po, path + ((z, 1),), act2))
        if nodes >= node_cap or (time_cap is not None and time.time() - t0 > time_cap):
            break
    neg = [v for v in viol if v[0] < 0]
    return dict(nodes=nodes, leaves=len(leaves), minleaf=minlb, violations=(neg if neg else viol[:5]),
                complete=(not stack), secs=time.time() - t0, leaf_paths=leaves if record else None,
                closures=closures if record else None, aborted=bool(neg))

