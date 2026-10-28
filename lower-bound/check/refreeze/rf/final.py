"""Assemble the verdict for a cover directory at a price:
  * every one of the 912 root families of roots_for_gap(30) has fam_<i>.json, complete, no violation, the same
    price SHA-256, exact minimum > 0 (each leaf: integer-checked lower bound minus E_block > 0);
  * each leaves_<i>.json.gz is re-read and its paths re-checked as a complete binary prefix code (Kraft sum 1);
  * the price: windows equal the frozen windows (lo, hi, U2 of pb/prices.json), phi_0 = 0, gamma_15 <= 0;
    Phi_0 recomputed exactly (pb/repair.packing) and the conditional scalar recomputed in exact rationals.
Writes cover_summary.json next to the price's cover directory. usage: final.py PRICE.json COVERDIR"""
import sys, os, json, gzip
from fractions import Fraction as Q
sys.path.insert(0, os.path.dirname(__file__))
from common import *
from cover import kraft
from roots import roots_for_gap
from repair import packing


def main():
    pf, od = sys.argv[1], sys.argv[2]
    price = json.load(open(pf)); ps = sha(pf); orig = json.loads((PB / 'prices.json').read_text())
    law = json.loads((PB / 'law.json').read_text()); n = law['n']
    assert price['lo'] == orig['lo'] and price['hi'] == orig['hi'] and price['U2'] == orig['U2']
    assert price['phi'][0] == 0 and price['gamma'][15] <= 0 and max(price['phi']) <= 0
    phi0, pat = packing(price)
    g = [Q.from_float(x) for x in price['gamma']]; total = n * (g[0] + g[15]) + 2 * n * sum(g[1:15], Q())
    ratio = (total + phi0 - Q(law['HXY_up']) - Q(law['HX_up']) - Q(law['HY_up'])) / Q(law['tau_up'])
    assert str(phi0) == price['exact_phi0'] and str(ratio) == price['conditional_ratio_lower']
    roots = roots_for_gap(n); fams = []; missing = []
    for i, r in enumerate(roots):
        f = os.path.join(od, f'fam_{i}.json')
        if not os.path.exists(f): missing.append(i); continue
        d = json.load(open(f))
        assert d['i'] == i and d['name'] == r[0] and d['complete'] and d['violation'] is None and d['price_sha256'] == ps
        assert d['exact_min'] is None or Q(d['exact_min']) > 0
        leaves = json.load(gzip.open(os.path.join(od, f'leaves_{i}.json.gz'), 'rt'))
        assert len(leaves) == d['leaves']; kraft(leaves)
        fams.append(dict(i=i, name=r[0], nodes=d['nodes'], leaves=d['leaves'], vacuous=d['vacuous'], seconds=round(d['seconds'], 2),
                         check_seconds=round(d['check_seconds'], 2), exact_min=d['exact_min_float'], retries=d['retries'], splits=d['splits']))
    tot_leaves = sum(f['leaves'] for f in fams); big = max(fams, key=lambda f: f['leaves']) if fams else None
    accepted = not missing
    out = dict(verdict='ACCEPTED' if accepted else 'INCOMPLETE', price=pf, price_sha256=ps,
               conditional_ratio_lower=str(ratio), conditional_ratio_display=float(ratio), exact_phi0=str(phi0),
               families_total=len(roots), families_complete=len(fams), missing=missing,
               total_nodes=sum(f['nodes'] for f in fams), total_leaves=tot_leaves,
               largest_family=big, total_seconds=sum(f['seconds'] for f in fams),
               min_exact_leaf_margin=min((f['exact_min'] for f in fams if f['exact_min'] is not None), default=None),
               families=fams)
    json.dump(out, open(os.path.join(od, 'cover_summary.json'), 'w'), indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != 'families'}, indent=1))


if __name__ == '__main__':
    main()
