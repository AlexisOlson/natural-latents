"""PACK-REPLAY-V4 deliverable 4: recompute price['exact_phi0'] and price['conditional_ratio_lower'] exactly.
Standard library only (`python -I scalar.py LAW PRICE`); derivation in SCALAR.md.

Phi_0 = inf { sum_i phi(m_i) : finite multiset of masses m_i in (0,1] summing to 1 },  phi(m) = phi_j on window
(lo_j/U2, hi_j/U2].  Computed as a minimum over integer unit counts s_i in [max(1, lo_j), hi_j] summing to U2 with at
least one s_i > lo_j (justification of both steps in SCALAR.md; it needs phi_0 = 0 and the windows to tile (0, 1]).
ratio = (sum_z gamma_z + Phi_0 - HXY_up - HX_up - HY_up) / tau_up.
"""
import sys, json
from fractions import Fraction as Q


def phi0(price):
    lo, hi, U2 = price['lo'], price['hi'], price['U2']
    phi = [Q(v) for v in price['phi']]                             # exact binary64 rationals
    assert lo[0] == 0 and hi[-1] == U2 and lo[1:] == hi[:-1] and all(a < b for a, b in zip(lo, hi))
    assert phi[0] == 0, 'the max(1, lo) step needs phi_0 = 0'
    D = 1
    for v in phi:
        D = D * v.denominator // __import__('math').gcd(D, v.denominator)
    cost = [int(v * D) for v in phi]
    INF = None
    # g[s][t]: least cost of a multiset of blocks with integer sizes summing to t; s = 1 once some size exceeds its lo
    g = [[INF] * (U2 + 1) for _ in range(2)]
    g[0][0] = 0
    moves = []                                                     # (size, strict?, cost) per window and size
    for j in range(len(lo)):
        for size in range(max(1, lo[j]), hi[j] + 1):
            moves.append((size, size > lo[j], cost[j], j))
    arg = [[None] * (U2 + 1) for _ in range(2)]
    for t in range(U2 + 1):                                        # sizes are >= 1, so increasing t is a topological order
        for s in (0, 1):
            cur = g[s][t]
            if cur is None:
                continue
            for size, strict, c, j in moves:
                u = t + size
                if u > U2:
                    continue
                s2 = 1 if (s or strict) else 0
                if g[s2][u] is None or cur + c < g[s2][u]:
                    g[s2][u] = cur + c; arg[s2][u] = (s, t, j)
    assert g[1][U2] is not None
    pat = {}; s, t = 1, U2
    while t:
        s0, t0, j = arg[s][t]; pat[str(j)] = pat.get(str(j), 0) + 1; s, t = s0, t0
    return Q(g[1][U2], D), pat


def main():
    law = json.load(open(sys.argv[1])); price = json.load(open(sys.argv[2]))
    n = law['n']
    P0, pat = phi0(price)
    gam = [Q(v) for v in price['gamma']]
    # orbit sizes: distance 0 and n/2 have n cells, distances 1..n/2-1 have 2n cells (n even)
    sizes = [n] + [2 * n] * (n // 2 - 1) + [n]
    assert sum(sizes) == n * n and len(gam) == n // 2 + 1
    total = sum(s * g for s, g in zip(sizes, gam))
    num = total + P0 - Q(law['HXY_up']) - Q(law['HX_up']) - Q(law['HY_up'])
    ratio = num / Q(law['tau_up'])
    out = dict(phi0=str(P0), phi0_float=float(P0), phi0_pattern=pat, phi0_matches_price=str(P0) == price['exact_phi0'],
               sum_gamma=str(total), numerator_positive=num > 0, ratio=str(ratio), ratio_float=float(ratio),
               ratio_matches_price=str(ratio) == price['conditional_ratio_lower'], ratio_gt_2=ratio > 2,
               modules_loaded=len(sys.modules))
    bad = [m for m in sys.modules if m.split('.')[0] in ('final', 'repair', 'common', 'numpy', 'runtime')]
    assert not bad, bad
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
