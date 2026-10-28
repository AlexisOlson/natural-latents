"""Search-phase kernels for the fibre cover (float64; the certified check is cert_check.py).

Claim at a node (A forced on, O forced off, free set W0): for every U = A + W, W within W0,
    G(U) = c(U) - gamma(U) = F0 - g0 + S(W) + psi(M),  psi(M) = M ln M,  M = m(A) + m(W),
    S(W) = Fsub(A+W) - Fsub(A) - gamma(W),  Fsub(V) = 2 sum_x h(r_x(V)) + 2 sum_y h(c_y(V))  (submodular in W).
For any x in the base polytope B(S) (any convex combination of greedy vertices):  S(W) >= x(W) >= sigma_x(m(W)),
sigma_x(mu) = min{ x(W') : W' fractional, m(W') = mu } (fractional knapsack: cells by x_e/p_e ascending).
So  G(U) >= F0 - g0 + min_mu [ sigma_x(mu) + psi(m(A)+mu) ]  -- a convex 1-d minimisation.
x is driven to the p-weighted minimum-norm point of B(S) (Wolfe, inner product sum x y / p), whose knapsack curve is
the convex envelope of mu -> min{S(W): m(W)=mu} (Fujishige), i.e. the best x for this bound.
"""
import numpy as np
from numba import njit


@njit(cache=False)
def hf(s):
    if s <= 0.0:
        return 0.0
    return -s * np.log(s)


@njit(cache=False)
def greedy(order, k, p, ri, ci, r0, c0, gfree, out):
    r = r0.copy(); c = c0.copy()
    for jj in range(k):
        e = order[jj]
        i = ri[e]; j = ci[e]
        rn = r[i] + p[e]; cn = c[j] + p[e]
        out[e] = 2.0 * (hf(rn) - hf(r[i])) + 2.0 * (hf(cn) - hf(c[j])) - gfree[e]
        r[i] = rn; c[j] = cn


@njit(cache=False)
def knap_bound(x, p, m0):
    """min over mu in [0, m(W0)] of sigma_x(mu) + psi(m0 + mu); returns (value, argmin mass mu, index of the
    knapsack cell whose segment holds the argmin, -1 if mu = 0)."""
    k = x.shape[0]
    rat = x / p
    order = np.argsort(rat)
    best = m0 * np.log(m0) if m0 > 0 else 0.0
    bmu = 0.0; bidx = -1
    mu = 0.0; s = 0.0
    for jj in range(k):
        e = order[jj]
        rho = rat[e]
        a = m0 + mu; b = m0 + mu + p[e]
        M = np.exp(-1.0 - rho)
        if M < a:
            M = a
        if M > b:
            M = b
        val = s + rho * (M - m0 - mu) + M * np.log(M)
        if val < best:
            best = val; bmu = M - m0; bidx = e
        mu += p[e]; s += x[e]
    return best, bmu, bidx


@njit(cache=False)
def wmnp(k, p, ri, ci, r0, c0, gfree, m0, base, target, maxit, init_order, maxk):
    """Wolfe min-norm point in the p-weighted norm.  Returns best bound found (base + knap_bound), its corral
    (orders as rows of an int array, weights), corral size, and best x."""
    V = np.zeros((maxk, k)); O = np.zeros((maxk, k), dtype=np.int64)
    Gm = np.zeros((maxk, maxk)); lam = np.zeros(maxk)
    ip = 1.0 / p
    q = np.zeros(k)
    greedy(init_order, k, p, ri, ci, r0, c0, gfree, q)
    V[0] = q; O[0] = init_order; Gm[0, 0] = np.sum(q * q * ip); lam[0] = 1.0; cnt = 1
    x = q.copy()
    best = -1e300; bestx = x.copy()
    bestO = O[:1].copy(); bestlam = lam[:1].copy(); bestcnt = 1
    for it in range(maxit):
        kb, _, _ = knap_bound(x, p, m0)
        val = base + kb
        if val > best:
            best = val; bestx = x.copy(); bestO = O[:cnt].copy(); bestlam = lam[:cnt].copy(); bestcnt = cnt
        if best >= target:
            break
        order = np.argsort(x * ip)
        greedy(order, k, p, ri, ci, r0, c0, gfree, q)
        xx = np.sum(x * x * ip); xq = np.sum(x * q * ip)
        if xx - xq <= 1e-12 * max(xx, 1e-30):
            break
        if cnt >= maxk:
            break
        V[cnt] = q; O[cnt] = order
        for j in range(cnt):
            g = np.sum(V[j] * q * ip)
            Gm[cnt, j] = g; Gm[j, cnt] = g
        Gm[cnt, cnt] = np.sum(q * q * ip)
        lam[cnt] = 0.0
        cnt += 1
        for minor in range(4 * maxk):
            # affine minimiser of the corral: alpha proportional to Gm^-1 1
            A = Gm[:cnt, :cnt].copy()
            tr = 0.0
            for j in range(cnt):
                tr += A[j, j]
            for j in range(cnt):
                A[j, j] += 1e-13 * tr / cnt
            y = np.linalg.solve(A, np.ones(cnt))
            alpha = y / y.sum()
            ok = True
            for j in range(cnt):
                if alpha[j] <= 1e-14:
                    ok = False
            if ok:
                for j in range(cnt):
                    lam[j] = alpha[j]
                break
            theta = 1.0
            for j in range(cnt):
                if alpha[j] <= 1e-14:
                    den = lam[j] - alpha[j]
                    if den > 0:
                        t = lam[j] / den
                        if t < theta:
                            theta = t
            for j in range(cnt):
                lam[j] = lam[j] + theta * (alpha[j] - lam[j])
            # drop (near-)zero weights, at least one
            jm = 0
            for j in range(cnt):
                if lam[j] < lam[jm]:
                    jm = j
            keep = 0
            for j in range(cnt):
                if lam[j] > 1e-14 and j != jm:
                    if keep != j:
                        V[keep] = V[j]; O[keep] = O[j]; lam[keep] = lam[j]
                    keep += 1
                elif j == jm and lam[j] > 1e-14 and False:
                    pass
            cnt = keep
            for j in range(cnt):
                for l2 in range(j, cnt):
                    g = np.sum(V[j] * V[l2] * ip)
                    Gm[j, l2] = g; Gm[l2, j] = g
            ssum = lam[:cnt].sum()
            for j in range(cnt):
                lam[j] /= ssum
            if cnt == 1:
                lam[0] = 1.0
                break
        x = np.zeros(k)
        for j in range(cnt):
            x += lam[j] * V[j]
    kb, _, _ = knap_bound(x, p, m0)
    if base + kb > best:
        best = base + kb; bestx = x.copy(); bestO = O[:cnt].copy(); bestlam = lam[:cnt].copy(); bestcnt = cnt
    return best, bestx, bestO, bestlam, bestcnt


@njit(cache=False)
def node_setup(on, off, P, ROW, COL, gam, n):
    N = P.shape[0]
    r0 = np.zeros(n); c0 = np.zeros(n); m0 = 0.0; g0 = 0.0; k = 0
    for z in range(N):
        if on[z]:
            r0[ROW[z]] += P[z]; c0[COL[z]] += P[z]; m0 += P[z]; g0 += gam[z]
        elif not off[z]:
            k += 1
    fz = np.zeros(k, dtype=np.int64)
    kk = 0
    for z in range(N):
        if (not on[z]) and (not off[z]):
            fz[kk] = z; kk += 1
    F0 = 0.0
    for i in range(n):
        F0 += 2.0 * hf(r0[i]) + 2.0 * hf(c0[i])
    p = P[fz].copy(); ri = ROW[fz].copy(); ci = COL[fz].copy(); gf = gam[fz].copy()
    return fz, p, ri, ci, gf, r0, c0, m0, F0 - g0


@njit(cache=False)
def G_mask(x, P, ROW, COL, gam, n):
    r = np.zeros(n); c = np.zeros(n); m = 0.0; g = 0.0
    for z in range(x.shape[0]):
        if x[z]:
            r[ROW[z]] += P[z]; c[COL[z]] += P[z]; m += P[z]; g += gam[z]
    t = 0.0
    for i in range(n):
        t += 2 * hf(r[i]) + 2 * hf(c[i])
    return t - hf(m) - g

