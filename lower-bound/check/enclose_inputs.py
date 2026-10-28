"""Directed input-enclosure check for the infinite and finite n=30 laws.

Run separately from verify.py. Requires mpmath. Prints JSON with exact endpoints,
script/input hashes and positive upper-end margins; assertion failure exits nonzero.
No output files are written. All operations and the infinite-tail estimate are
visible here; no proposer or checker implementation is imported.
"""
import hashlib
import json
from pathlib import Path
from fractions import Fraction as Q
from mpmath import mp, iv

ROOT=Path(__file__).resolve().parents[1]
mp.dps=160
n=30
law=json.loads((ROOT/'data/law.json').read_text())
tr=json.loads((ROOT/'data/transfer.json').read_text())
def mpr(s):
    q=Q(s)
    return mp.mpf(q.numerator)/q.denominator
# Directed arithmetic, with explicit positive infinite tail. For d<=15,
# omitted aliases beyond r=-2..2 start at |j+30r|>=90-d; successive terms
# have ratio <1/2, hence the two tails sum to <=4 exp(-alpha*(90-d)^2).
iv.dps=115
def ivq(s):
    q=Q(s)
    return iv.mpf(q.numerator)/q.denominator
def exact_endpoint(x,upper=False):
    sign,man,exp,bc=x._mpi_[int(upper)]
    return Q((-1 if sign else 1)*int(man)) * Q(2)**exp
def hull(lo,hi):
    return iv.mpf([lo.a,hi.b])
def dft_even(a):
    return [a[0]+((-1)**x)*a[15]+2*sum(a[j]*iv.cos(2*iv.pi*j*x/n) for j in range(1,15)) for x in range(n)]
def entropy(vals):
    return -sum(v*iv.ln(v) for v in vals)
def interval_audit(finite):
    al=ivq(Q(3502021035450561,2**53))
    half=[]
    for d in range(16):
        if finite:
            v=iv.exp(-al*d*d)+iv.exp(-al*(30-d)**2)
        else:
            central=sum(iv.exp(-al*(d+30*r)**2) for r in range(-2,3))
            tail=4*iv.exp(-al*(90-d)**2)
            v=hull(central,central+tail)
        half.append(v)
    a=half+half[14:0:-1]
    b=[sum(a[k]*a[(j-k)%n] for k in range(n)) for j in range(n)]
    # b_j=b_-j as an exact identity; use one enclosure for either member.
    b=b[:16]+b[14:0:-1]
    m2=b[0]; m3=sum(a[j]*b[-j%n] for j in range(n))
    rho=dft_even(a)
    lam=[m2*a[j]/b[j] for j in range(n)]
    ker=dft_even(lam)
    assert all(exact_endpoint(v)>0 for v in rho+ker)
    q=[[ker[(x-y)%n]*rho[x]**2*rho[y]**2/(n*n*m2*m3) for y in range(n)] for x in range(n)]
    pd=[sum(q[x][(x+d)%n] for x in range(n))/n for d in range(n)]
    qx=[sum(row) for row in q]
    qy=[sum(q[x][y] for x in range(n)) for y in range(n)]
    HXY=n*entropy(pd); HX=iv.ln(iv.mpf(n)); HY=HX
    HQ=entropy([p for row in q for p in row])
    tau=2*HXY-2*iv.ln(iv.mpf(n))+2*entropy(qx)+2*entropy(qy)-3*HQ
    ins=all(Q(law['pd_lo'][d])<=exact_endpoint(pd[d]) and exact_endpoint(pd[d],True)<=Q(law['pd_up'][d]) for d in range(n))
    delta=n*sum(max(abs(exact_endpoint(pd[d])-Q(law['p_int'][d],2**52)),abs(exact_endpoint(pd[d],True)-Q(law['p_int'][d],2**52))) for d in range(n))
    delta_stored=Q(tr['delta']); di=ivq(delta_stored)
    eb= -4*n*(di/n)*iv.ln(di/n)-di*iv.ln(di)
    bounds={}
    for name,v in [('HXY',HXY),('HX',HX),('HY',HY),('tau',tau)]:
        upper=Q(law[name+'_up'])
        lo=exact_endpoint(v); hi=exact_endpoint(v,True)
        slack=upper-hi
        bounds[name]={'lo':str(lo),'up':str(hi),'stored_upper_slack':str(slack),
             'slack_display':mp.nstr(mpr(slack),12),'width_display':mp.nstr(mpr(hi-lo),12),'mid_display':mp.nstr(mpr((lo+hi)/2),45),
             'bits_display':mp.nstr(mpr((lo+hi)/2)/mp.log(2),25)}
        assert slack>0
    assert ins and delta<delta_stored and exact_endpoint(eb,True)<Q(tr['error'])
    assert exact_endpoint(tau)>Q(law['tau_lo'])>0
    return {'interval_digits':iv.dps,'inside_all_pd_boxes':ins,'all_rho_K_positive':True,
       'rho_min_lower_display':mp.nstr(min(mpr(exact_endpoint(v)) for v in rho),20),
       'K_min_lower_display':mp.nstr(min(mpr(exact_endpoint(v)) for v in ker),20),
       'delta_slack_display':mp.nstr(mpr(delta_stored-delta),15),
       'error_slack_display':mp.nstr(mpr(Q(tr['error'])-exact_endpoint(eb,True)),15),
       'bounds':bounds}

sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={'script_sha256':sha(Path(__file__)),
        'law_sha256':sha(ROOT/'data/law.json'),
        'transfer_sha256':sha(ROOT/'data/transfer.json'),
        'finite':interval_audit(True),'infinite':interval_audit(False)}
print(json.dumps(report,indent=2))
