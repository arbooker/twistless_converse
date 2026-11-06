"""Exact transport of original Hecke2 through the three-term A trace."""
from pathlib import Path
from collections import deque
import json, resource, hashlib
resource.setrlimit(resource.RLIMIT_CPU,(25,26))
resource.setrlimit(resource.RLIMIT_AS,(550*1024**2,550*1024**2))
base=Path(__file__).resolve().parent
src=base/'level27_root_chi5_defect.py'
n={};exec(src.read_text().split("words=['sRssr'")[0],n)
I,R,S=n['I'],n['R'],n['S']; mul,inv,norm=n['mul'],n['inv'],n['norm']
alphas=[(1,0,0,2),(1,3,0,2),(2,0,0,1)]
gammas=[S,mul(S,R),mul(mul(S,R),R)]
det=lambda m:m[0]*m[3]-m[1]*m[2]
data=[]; need=set()
for ga in gammas:
    for i,al in enumerate(alphas):
        candidates=[]
        for j,be in enumerate(alphas):
            m=mul(mul(al,ga),inv(be))
            if det(m)==1 and m[2]%3==0:candidates.append((j,m))
        assert len(candidates)==1,candidates
        j,m=candidates[0];data.append((ga,i,j,m));need.add(m)
words={I:''};queue=deque([I])
while need-words.keys():
    m=queue.popleft();word=words[m]
    assert len(word)<10,(word,need-words.keys())
    for c,G in n['gens'].items():
        t=mul(m,G)
        if t not in words:words[t]=word+c;queue.append(t)
states=[[0]*4 for a in alphas];op={};rows=[]
for ga,i,j,m in data:
    actual,v,aop=n['expand'](words[m]);assert actual==m
    for k,c in enumerate(v):states[j][k]+=c
    for H,c in aop.items():n['accum'](op,mul(H,alphas[j]),c)
    rows.append({'gamma':ga,'branch':i,'new_branch':j,'word':words[m],
                 'matrix':m,'state':v,'A_terms':[[H,c] for H,c in aop.items()]})
N=(20,-1,-15,2);E=(2,4,-3,-4);J=n['J']
def c6(op,eta):
    syms=[];e=I
    for i in range(3):
        syms.extend([(e,1),(mul(e,J),-eta)]);e=mul(e,E)
    out={}
    for m,c in op.items():
        mm,ch=min((mul(h,m),ch) for h,ch in syms)
        n['accum'](out,mm,ch*c)
    return out
out={'status':'PASS_EXACT_HECKE2_TRANSPORT','state_remainders':states,
     'A_operator':[[H,c] for H,c in sorted(op.items())],
     'c6_reduced':{str(eta):[[H,c] for H,c in sorted(c6(op,eta).items())] for eta in [1,-1]},
     'rows':rows,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest()}
Path('/tmp/level27_continuation_geometry_hecke.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
