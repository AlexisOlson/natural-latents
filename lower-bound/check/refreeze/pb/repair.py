"""Exact finite mass packing before/after a componentwise penalty reduction.
A proposal repair is not an all-block certificate.
"""
import runtime,json,time
from fractions import Fraction as Q
from collections import Counter

def packing(price):
    ph=list(map(Q.from_float,price['phi'])); den=max(v.denominator for v in ph); cost=[int(v*den) for v in ph]
    assert all(Q(c,den)==v for c,v in zip(cost,ph)) and ph[0]>=0
    N=price['U2']; f=[[None]*(N+1) for _ in range(2)]; pred=[[None]*(N+1) for _ in range(2)]; f[0][0]=0
    for a in range(N):
        for flag in (0,1):
            old=f[flag][a]
            if old is None: continue
            for j,(lo,hi) in enumerate(zip(price['lo'],price['hi'])):
                if max(1,lo)>N-a: break
                for step in range(max(1,lo),min(hi,N-a)+1):
                    ff=int(flag or step>lo); aa=a+step; value=old+cost[j]
                    if f[ff][aa] is None or value<f[ff][aa]: f[ff][aa]=value; pred[ff][aa]=(a,flag,j,step)
    assert f[1][N] is not None
    a=N; flag=1; pattern=[]
    while a:
        a0,flag0,j,step=pred[flag][a]; pattern.append(j); a=a0; flag=flag0
    return Q(f[1][N],den),dict(Counter(pattern))

def main():
    orig=json.loads((runtime.OUT/'prices.json').read_text()); clipped=json.loads(json.dumps(orig)); clipped['phi']=[min(v,0.) for v in orig['phi']]
    start=time.perf_counter(); before,p0=packing(orig); after,p1=packing(clipped)
    scalar=dict(original_phi0=str(before),clipped_phi0=str(after),difference=str(after-before),original_pattern=p0,clipped_pattern=p1,seconds=time.perf_counter()-start,positive_windows=sum(v>0 for v in orig['phi']),claim='exact packing scalar only; complete block feasibility remains unverified')
    clipped['source_frozen_price_sha256']=runtime.hashes([runtime.OUT/'prices.json'])['out\\prices.json']; clipped['repair']='cap every positive phi at zero; gamma unchanged'
    runtime.save('prices_positive_capped.json',clipped); runtime.save('repair_scalar.json',scalar)
    runtime.log('REPAIR_SCALAR '+json.dumps(scalar))
if __name__=='__main__': main()
