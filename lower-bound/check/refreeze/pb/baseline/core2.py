"""Faster Wolfe min-norm point (p-weighted) with incremental Cholesky (add: forward solve; delete: rank-1 update),
plus an early stop when a real fibre inside the node already has G < target (the node cannot close).
Search phase only: validity of any returned bound rests on x being a convex combination of greedy vertices, which
cert_check.py re-establishes independently."""
import numpy as np
from numba import njit
from core import hf, greedy, knap_bound


@njit(cache=False)
def chol_add(L, cnt, g, gqq):
    l = np.zeros(cnt)
    for i in range(cnt):
        s = g[i]
        for j in range(i):
            s -= L[i, j] * l[j]
        l[i] = s / L[i, i]
    d = gqq - np.dot(l, l)
    if d <= 1e-13 * gqq:
        return False
    for j in range(cnt):
        L[cnt, j] = l[j]
    L[cnt, cnt] = np.sqrt(d)
    return True


@njit(cache=False)
def chol_del(L, cnt, j):
    m = cnt - j - 1
    w = np.zeros(m)
    for t in range(m):
        w[t] = L[j + 1 + t, j]
    for i in range(j, cnt - 1):
        for c in range(0, j):
            L[i, c] = L[i + 1, c]
        for c in range(j, i + 1):
            L[i, c] = L[i + 1, c + 1]
    for kk in range(m):
        i = j + kk
        Lii = L[i, i]
        r = np.sqrt(Lii * Lii + w[kk] * w[kk])
        c = r / Lii; s = w[kk] / Lii
        L[i, i] = r
        for t in range(kk + 1, m):
            ii = j + t
            L[ii, i] = (L[ii, i] + s * w[t]) / c
            w[t] = c * w[t] - s * L[ii, i]
    for c in range(L.shape[1]):
        L[cnt - 1, c] = 0.0


@njit(cache=False)
def chol_solve_ones(L, cnt):
    y = np.zeros(cnt)
    for i in range(cnt):
        s = 1.0
        for j in range(i):
            s -= L[i, j] * y[j]
        y[i] = s / L[i, i]
    z = np.zeros(cnt)
    for i in range(cnt - 1, -1, -1):
        s = y[i]
        for j in range(i + 1, cnt):
            s -= L[j, i] * z[j]
        z[i] = s / L[i, i]
    return z


@njit(cache=False)
def S_of(sel, k, p, ri, ci, r0, c0, gfree, n):
    """S(W) = Fsub(A+W) - Fsub(A) - gamma(W) for W = {e : sel[e]}; returns (S, m(W))."""
    r = r0.copy(); c = c0.copy(); g = 0.0; mw = 0.0
    for e in range(k):
        if sel[e]:
            r[ri[e]] += p[e]; c[ci[e]] += p[e]; g += gfree[e]; mw += p[e]
    t = 0.0
    for i in range(n):
        t += 2.0 * (hf(r[i]) - hf(r0[i])) + 2.0 * (hf(c[i]) - hf(c0[i]))
    return t - g, mw


@njit(cache=False)
def wmnp2(k, p, ri, ci, r0, c0, gfree, m0, base, target, maxit, init_order, maxk, n, witness_every):
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
    status = 0  # 0 maxit, 1 closed, 2 witness below target, 3 converged
    sel = np.zeros(k, dtype=np.bool_)
    for it in range(maxit):
        kb, mu, bidx = knap_bound(x, p, m0)
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
            gw = base + Sw + M * np.log(M)
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
            # delete jdel
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
    kb, mu, bidx = knap_bound(x, p, m0)
    if base + kb > best:
        best = base + kb; bestx = x.copy(); bestO = O[:cnt].copy(); bestlam = lam[:cnt].copy()
    return best, bestx, bestO, bestlam, status, wit

