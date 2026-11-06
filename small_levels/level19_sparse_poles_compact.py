"""Exact sparse compactification of the audited N19 equal-sign constraints.
No symbolic simplification or modular computation.  Output remains under /tmp.
Each original polynomial equals x**(dx+da)*y**dy*a**da times its compact
polynomial evaluated at (B,A,Z,Y,X)=(by,ax,z,y²,x²), up to rational scale.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import re,json,hashlib
src=Path('/tmp/deterministic_gb_audit_n19_equal_constraints.m')
s=src.read_text().replace('\\\n','').replace('\n','')
s=s.split('P:=',1)[1].strip().removeprefix('[').removesuffix(';').removesuffix(']')
vs=['x','y','z','a','b']; out=[]; records=[]; seen=set()
for i,p in enumerate(s.split(',')):
    d=defaultdict(F)
    for term in re.findall(r'[+-]?[^+-]+',p.replace(' ','')):
        c=F(1); e=[0]*5
        if term[0]=='-':c=-c;term=term[1:]
        elif term[0]=='+':term=term[1:]
        for f in term.split('*'):
            if f[0] in vs:
                v,*a=f.split('^');e[vs.index(v)]+=int(a[0]) if a else 1
            else:c*=F(f)
        d[tuple(e)]+=c
    d={e:c for e,c in d.items() if c}
    dx=min(e[0]-e[3] for e in d);dy=min(e[1]-e[4] for e in d);da=min(e[3] for e in d)
    q={}
    for e,c in d.items():
        assert (e[0]-e[3]-dx)%2==0 and (e[1]-e[4]-dy)%2==0
        v=(e[4],e[3]-da,e[2],(e[1]-e[4]-dy)//2,(e[0]-e[3]-dx)//2)
        assert min(v)>=0 and v not in q
        q[v]=c
        # Exact inverse monomial reconstruction, independent of parity test.
        ee=(2*v[4]+v[1]+dx+da,2*v[3]+v[0]+dy,v[2],v[1]+da,v[0])
        assert ee==e
    scale=q[min(q)];q={e:c/scale for e,c in q.items()}
    key=tuple(sorted(q.items()))
    if key in seen:continue
    seen.add(key);out.append(q)
    records.append(dict(source_index=i+1,factor_x=dx+da,factor_y=dy,factor_a=da,scale=str(scale),terms=len(q)))
def fmt(q):
    terms=[]
    for e,c in sorted(q.items()):
        term=str(c)+''.join('*'+v+(('^'+str(a)) if a!=1 else '') for v,a in zip(['B','A','Z','Y','X'],e) if a)
        terms.append(term)
    return '+'.join(terms).replace('+-','-')
target=Path('/tmp/level19_sparse_poles_compactall_polys.m')
target.write_text('S<B,A,Z,Y,X>:=PolynomialRing(Rationals(),5,"grevlex");\nPP:=['+','.join(fmt(q) for q in out)+'];\n')
meta=dict(input_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),count=len(out),rows=records)
Path('/tmp/level19_sparse_poles_compactall_manifest.json').write_text(json.dumps(meta,indent=2))
print('EXACT INVERSE MONOMIAL IDENTITIES PASS',len(out),target.stat().st_size)
print([(j+1,len(q),max(e[2] for e in q)) for j,q in enumerate(out)])
sparse=Path('/tmp/level19_sparse_poles_compactall_fast.m')
sparse.write_text('S<B,A,Z,Y,X>:=PolynomialRing(Rationals(),5,"grevlex");\nPP:=[S|];\n'+''.join('Append(~PP,Polynomial(['+','.join(str(c) for e,c in sorted(q.items()))+'],[Monomial(S,e):e in ['+','.join(str(list(e)) for e,c in sorted(q.items()))+']]));\n' for q in out))
print('FAST',sparse.stat().st_size)
