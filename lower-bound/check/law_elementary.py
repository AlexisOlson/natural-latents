"""Builds the finite elementary law of PROOF.md section 1 at 400 digits and checks that every p_d lies inside the stored
enclosures pd_lo/pd_up of data/law.json. Also compares it with the infinite-alias law (a_j summed over all j + 30r).
usage: python law_elementary.py [path/to/law.json]   (standard library + mpmath; exit 0 only if every check passes)"""
import json, os, sys
from fractions import Fraction
from mpmath import mp, mpf, exp, cos, pi
mp.dps = 400
n = 30; alpha = mpf(3502021035450561) / 2**53
law = json.load(open(sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data', 'law.json')))
def build(a):                                   # a_j (j = 0..29) -> the 30 values p_d = u_d v_d / Z
    b = [sum(a[k] * a[(j - k) % n] for k in range(n)) for j in range(n)]
    u = [sum(a[j] / b[j] * cos(2 * pi * j * d / n) for j in range(n)) for d in range(n)]
    v = [sum(b[j] ** 2 * cos(2 * pi * j * d / n) for j in range(n)) for d in range(n)]
    Z = n * sum(u[d] * v[d] for d in range(n)); return [u[d] * v[d] / Z for d in range(n)]
fin = build([exp(-alpha * j * j) + exp(-alpha * (n - j) ** 2) for j in range(n)])
inf = build([sum(exp(-alpha * (j + n * r) ** 2) for r in range(-60, 61)) for j in range(n)])
fr = lambda s: mpf(Fraction(s).numerator) / Fraction(s).denominator
lo = [fr(s) for s in law['pd_lo']]; up = [fr(s) for s in law['pd_up']]
inside = lambda p: all(lo[d] <= p[d] <= up[d] for d in range(n))
print('alpha = 3502021035450561/2^53; digits:', mp.dps, '; sum over the 900 cells - 1 =', mp.nstr(n * sum(fin) - 1, 5))
print('every finite-law p_d inside [pd_lo, pd_up]:', inside(fin), '; every infinite-alias p_d inside:', inside(inf))
print('max relative width of the enclosures (up-lo)/lo:', mp.nstr(max((up[d] - lo[d]) / lo[d] for d in range(n)), 5))
print('max relative difference finite vs infinite-alias law:', mp.nstr(max(abs(fin[d] - inf[d]) / inf[d] for d in range(n)), 5))
print('p_0 =', mp.nstr(fin[0], 12), ' p_15 =', mp.nstr(fin[15], 6), ' p_0 * 2^52 =', mp.nstr(fin[0] * 2**52, 15), ' (p_int[0] =', law['p_int'][0], ')')
sys.exit(0 if inside(fin) and inside(inf) else 1)
