"""Bounded exact monomial elimination for the N25 Q1050 prime-7 extension.
Exploratory unless the closing assertions explicitly certify a theorem.
"""
from pathlib import Path
import sys,time
base=Path(__file__).parent
aux=(base/'level25_finish_augmented.py').read_text()
exec(aux[:aux.index("src=Path")])
src=(base/'level25_uniform_continuation.py').read_text()
src=src[:src.index("print('rows'")]
src=src.replace("K,x,y,z,a,b=field('x,y,z,a,b',QQ)","K,x,y,z,w,a,b,lam7=field('x,y,z,w,a,b,lam7',QQ)")
src=src.replace('N=25;Q=150','N=25;Q=1050')
src=src.replace('V={2:x,3:y,5:z}','V={2:x,3:y,5:z,7:w}')
src=src.replace('[(2,a),(3,b),(5,K.zero)]','[(2,a),(3,b),(5,K.zero),(7,lam7)]')
src=src.replace('for A,B,C,D in known(N,3):','for (A,B,C,D),mu in known_aug(N,3):')
src=src.replace('c=mon(Fraction(den,Q))**2','c=mu*mon(Fraction(den*den,(A*D-B*C)*Q*Q))')
src=src.replace("('g',A,B,C,D,j)","('g',A,B,C,D,mu,j)")
exec(src)
if 'old150' in sys.argv:
    for j in range(150):R.append(({7*j:K.one},('old150',j)))
original=[(dict(row),lab) for row,lab in R]
print('SYMBOLIC_BUILT',eta,'rows',len(R),flush=True)
def safe(v):
    return len(v.numer.terms())==len(v.denom.terms())==1 and not any(v.numer.terms()[0][0][4:]) and not any(v.denom.terms()[0][0][4:])
piv=[];start=time.monotonic()
while R:
    chosen=None
    for i,(row,lab) in enumerate(R):
        if (chosen is None or len(row)<len(R[chosen][0])) and any(safe(v) for v in row.values()):chosen=i
    if chosen is None:break
    row,lab=R.pop(chosen)
    col=min((j for j,v in row.items() if safe(v)),key=lambda j:sum(j in rr for rr,ll in R))
    val=row[col];row={j:v/val for j,v in row.items()};piv.append((col,row,lab));new=[]
    for rr,ll in R:
        if col in rr:
            co=rr[col]
            for j,v in row.items():
                rr[j]=rr.get(j,K.zero)-co*v
                if not rr[j]:del rr[j]
        if rr:new.append((rr,ll))
    R=new
    if len(piv)%100==0:print('PIVOTS',len(piv),'rows',len(R),'seconds',round(time.monotonic()-start,1),flush=True)
    if time.monotonic()-start>180:raise TimeoutError('bounded symbolic elimination')
free=sorted(set(range(Q))-{j for j,row,lab in piv})
print('MONOMIAL_RESULT',len(piv),'free_count',len(free),'residual',len(R),'free',free,flush=True)
if 'old150' in sys.argv:
    assert not R,'Residual conditions remain; no all-parameter source-free kernel theorem'
    for col in free:
        pole=[K.zero]*Q;pole[col]=K.one
        for j,row,lab in reversed(piv):pole[j]=-sum((v*pole[c] for c,v in row.items() if c!=j),K.zero)
        assert all(not pole[j] for j in range(0,Q,7))
        for row,lab in original:
            assert sum((v*pole[j] for j,v in row.items()),K.zero)==0
            if lab[0]=='g':
                _,A,B,C,D,mu,j=lab;den=C*j+D*Q;dest=Q*(A*j+B*Q)//den%Q
                assert C==0 or pole[dest]==0
            if lab[0]=='F':
                _,q,t=lab;ell=lcm(N,q*q);u=-(Q*Q//ell)//t
                assert sum((pole[(v*(Q//q)+u)%Q] for v in range(q) if gcd(v,q)==1),K.zero)==0
    print('EXACT_ALL_PARAMETER_SOURCE_FREE_KERNEL_VERIFIED',eta,len(free),flush=True)
