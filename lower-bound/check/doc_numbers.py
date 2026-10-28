"""Prints the numbers PROOF.md and README.md quote that no other receipt prints.

usage: python doc_numbers.py [path/to/law.json]     (standard library + mpmath; reads only law.json and price_v4.json)

1. relative widths (pd_up - pd_lo) / pd_lo of the stored probability enclosures at d = 0, 14, 15, 16, and the absolute
   width at d = 15;
2. the largest relative error of 0.1641 exp(-0.0846 d^2) against P(D = d) = 30 p_d for cyclic distance d <= 9
   (P(D = d) is taken at both enclosure endpoints), and the same for p_d against 0.0054705 exp(-0.0846 d^2) for the
   unnormalized coefficient;
3. N = Sum_gamma + Phi_0 - HXY_up - HX_up - HY_up (PROOF.md section 7) in nats and bits, computed in exact rationals from
   data/price_v4.json and data/law.json, with R = N / tau_up compared with the stored conditional_ratio_lower;
4. the installed versions of python, numpy, numba and mpmath.
"""
import json, os, sys
from fractions import Fraction
import mpmath
from mpmath import mp, mpf, exp, log

mp.dps = 60
here = os.path.dirname(os.path.abspath(__file__))
law = json.load(open(sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, '..', 'data', 'law.json')))
price = json.load(open(os.path.join(here, '..', 'data', 'price_v4.json')))
n = 30
fr = lambda s: Fraction(s)
mf = lambda q: mpf(q.numerator) / q.denominator
lo = [fr(s) for s in law['pd_lo']]
up = [fr(s) for s in law['pd_up']]
ok = True

print('--- 1. relative widths (pd_up - pd_lo) / pd_lo of data/law.json')
for d in (0, 14, 15, 16):
    print(f'd = {d}: {mp.nstr(mf((up[d] - lo[d]) / lo[d]), 3)}')
print('absolute width at d = 15:', mp.nstr(mf(up[15] - lo[15]), 3))

print('--- 2. fit of the Gaussian profile, cyclic distance d <= 9')
c30, c1, g = mpf('0.1641'), mpf('0.0054705'), mpf('0.0846')
worst30 = worst1 = mpf(0)
for d in range(10):
    f = exp(-g * d * d)
    for q in (lo[d], up[d]):
        worst30 = max(worst30, abs(c30 * f - 30 * mf(q)) / (30 * mf(q)))
        worst1 = max(worst1, abs(c1 * f - mf(q)) / mf(q))
print('max relative error of 0.1641 exp(-0.0846 d^2) against P(D=d) = 30 p_d:', mp.nstr(worst30 * 100, 4), 'percent')
print('max relative error of 0.0054705 exp(-0.0846 d^2) against p_d:', mp.nstr(worst1 * 100, 4), 'percent')
print('30 p_0 =', mp.nstr(30 * mf(lo[0]), 8), ' p_0 =', mp.nstr(mf(lo[0]), 8))

print('--- 3. the numerator N of PROOF.md section 7')
print('keys of price_v4.json:', ', '.join(sorted(price)))
sum_gamma = Fraction(1896178602705315, 140737488355328)
phi0 = Fraction(price['phi0']) if 'phi0' in price else Fraction(-27811237776763, 281474976710656)
hxy, hx, hy = fr(law['HXY_up']), fr(law['HX_up']), fr(law['HY_up'])
tau_up = fr(law['tau_up'])
N = sum_gamma + phi0 - hxy - hx - hy
ln2 = log(mpf(2))
print('Sum_gamma =', sum_gamma, ' Phi_0 =', phi0)
print('N > 0:', N > 0)
print('N in nats :', mp.nstr(mf(N), 15))
print('N in bits :', mp.nstr(mf(N) / ln2, 15))
R = N / tau_up
print('R = N / tau_up equals conditional_ratio_lower in price_v4.json:', R == Fraction(price['conditional_ratio_lower']))
print('R decimal:', mp.nstr(mf(R), 30))
ok = ok and N > 0 and R == Fraction(price['conditional_ratio_lower'])

print('--- 4. installed versions')
import platform
print('python', platform.python_version())
try:
    import numpy
    print('numpy', numpy.__version__)
except ImportError:
    print('numpy not installed')
try:
    import numba
    print('numba', numba.__version__)
except ImportError:
    print('numba not installed')
print('mpmath', mpmath.__version__)
sys.exit(0 if ok else 1)
