"""Certified upper bound on T(p) from one explicit deterministic code, for the n = 30 law.

For a code G = g(X) that groups the circle into consecutive blocks, the cost
D(G) = I(X;Y|G) + H(G|X) + H(G|Y) reduces (X, Y uniform, H(G|X) = 0) to
    D(G) = 2 H(G,Y) - H(G) - H(X,Y) - H(Y) + H(X) = 2 H(G,Y) - H(G) - H(q) - ln 30,
where q_d = P(D = d) = 30 p_d. Any code's cost is an upper bound on T(p), so T(p) <= D(G).
The search is float64 and only picks the code; the certified value uses mpmath interval arithmetic over the
enclosures pd_lo/pd_up of law.json, which contain the true law.
Usage: python code_upper.py <law.json>
"""
import json, sys, itertools, math
from fractions import Fraction
from mpmath import iv

iv.dps = 60
n = 30
law = json.load(open(sys.argv[1]))
lo = [Fraction(s) for s in law["pd_lo"]]
up = [Fraction(s) for s in law["pd_up"]]
tau_lo, tau_up = Fraction(law["tau_lo"]), Fraction(law["tau_up"])

def ivf(a, b):
    return iv.mpf([iv.mpf(a.numerator) / a.denominator, iv.mpf(b.numerator) / b.denominator])

def blocks_of(sizes):
    out, x = [], 0
    for s in sizes:
        out.append(list(range(x, x + s)))
        x += s
    return out

qf = [float(15 * (lo[d] + up[d])) for d in range(n)]
def hf(t):
    return -t * math.log(t) if t > 0 else 0.0
def cost_f(sizes):
    bl = blocks_of(sizes)
    HG = sum(hf(len(B) / n) for B in bl)
    HGY = sum(hf(sum(qf[(y - x) % n] for x in B) / n) for B in bl for y in range(n))
    return 2 * HGY - HG - sum(hf(t) for t in qf) - math.log(n)

# By circulance a consecutive block's contribution depends only on its size, so the cost of a code by
# consecutive blocks depends only on the multiset of sizes: search the integer partitions of 30 into <= 10 parts.
def partitions(total, maxpart, parts):
    if total == 0:
        yield []
        return
    if parts == 0:
        return
    for s in range(min(total, maxpart), 0, -1):
        for rest in partitions(total - s, s, parts - 1):
            yield [s] + rest

best = None
for sizes in partitions(n, n, 10):
    c = cost_f(sizes)
    if best is None or c < best[0]:
        best = (c, sizes)
print("best consecutive-block code (float search):", best[1], best[0] / math.log(2), "bits", flush=True)

q = [ivf(30 * lo[d], 30 * up[d]) for d in range(n)]
def h_iv(t):
    return -t * iv.log(t)
bl = blocks_of(best[1])
HG = sum(h_iv(iv.mpf(len(B)) / n) for B in bl)
HGY = sum(h_iv(sum(q[(y - x) % n] for x in B) / n) for B in bl for y in range(n))
Hq = sum(h_iv(t) for t in q)
D = 2 * HGY - HG - Hq - iv.log(iv.mpf(n))
ln2 = iv.log(iv.mpf(2))
print("code: consecutive blocks of X, sizes", best[1])
print("certified D(G), nats:", D)
print("certified D(G), bits:", D / ln2)
print("tau_L enclosure, nats:", ivf(tau_lo, tau_up))
print("certified upper bound on T(p)/tau_L (D_up / tau_L_lo):", (D / ivf(tau_lo, tau_lo)).b)
