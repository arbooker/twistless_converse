"""Direct Q[lambda] right-ideal certificate for the affine A equation."""
from pathlib import Path
from fractions import Fraction as F
import json, hashlib, resource
resource.setrlimit(resource.RLIMIT_CPU,(25,26))
resource.setrlimit(resource.RLIMIT_AS,(550*1024**2,550*1024**2))
base=Path(__file__).resolve().parent
source=base/'level27_bridge_chi5_finish_check.py'
n={};exec(source.read_text().split('# Independently replay')[0],n)
I,R,S,r,ss=[n[x] for x in ['I','R','S','r','s']]
mat,inv,add,right,atom=[n[x] for x in ['mat','inverse','add','right','atom']]
PR,PS,C,A,DU=[n[x] for x in ['PR','PS','C','A','DU']]
rels=[PR,PS,C,DU]
def cp(*parts):
    ans={}
    for scale,part in parts:
        for tag,v in part.items():ans[tag]=ans.get(tag,F(0))+scale*v
    return {t:v for t,v in ans.items() if v}
def term(gen,m=I,c=1,deg=0):return {(gen,m,deg):F(c)}
def cr(p,m):return {(g,mat(a,m),d):v for (g,a,d),v in p.items()}
last=cp((1,term(1,R)),(-1,term(2,S)),(-1,term(2)),(-1,term(3)))
rowcert={
 'R':[{},term(0),term(2),term(0,S)],
 'S':[{}, {},term(1),last],
 'r':[term(0,r),{},cp((1,term(0,mat(S,r))),(1,term(2,r))),term(2,r,-1)],
 's':[term(1,ss),cr(last,ss),{},{}]}
def evalcert(cert):
    out={}
    for (gi,m,d),v in cert.items():
        for a,c in right(rels[gi],m).items():
            tag=(a,d);out[tag]=out.get(tag,F(0))+v*c
    return {t:v for t,v in out.items() if v}
for letter in rowcert:
    for i,cert in enumerate(rowcert[letter]):
        assert evalcert(cert)=={(m,0):v for m,v in n['certificates'][letter][i].items()}
# Recover a small independent certificate for DU from PR,PS,C only.
words={I};front={I}
for _ in range(5):
    front={mat(m,t) for m in front for t in [R,r,S,ss]}-words
    words.update(front)
basis={};provenance={};order=[]
def reduce(poly):
    out=dict(poly);used=[]
    while out:
        p=max(out)
        if p not in basis:break
        c=out[p];used.append((p,c));out=add((1,out),(-c,basis[p]))
    return out,used
for m in sorted(words):
    for gi,rel in enumerate(rels[:3]):
        out,used=reduce(right(rel,m))
        if out:
            p=max(out);c=out[p];basis[p]={a:v/c for a,v in out.items()}
            provenance[p]=((gi,m,0),c,used);order.append(p)
rem,used=reduce(DU);assert not rem
weights={};ducert={}
for p,c in used:weights[p]=weights.get(p,F(0))+c
for p in reversed(order):
    v=weights.pop(p,F(0))
    if not v:continue
    tag,c,anc=provenance[p];v/=c;ducert[tag]=ducert.get(tag,F(0))+v
    for q,b in anc:weights[q]=weights.get(q,F(0))-v*b
ducert={t:v for t,v in ducert.items() if v}
assert not any(weights.values())
assert evalcert(ducert)=={(m,0):v for m,v in DU.items()}
data=json.loads(Path('/tmp/level27_continuation_geometry_hecke.json').read_text())
cert={};op={};states={}
for row in data['rows']:
    word=row['word'];v=[1,0,0,0];error={};aop={};actual=I
    for letter in word:
        error=cr(error,n['letters'][letter]);new=right(aop,n['letters'][letter]);vv=[0]*4
        for i,c in enumerate(v):
            ve,ae=n['table'][letter][i]
            error=cp((1,error),(c,rowcert[letter][i]))
            vv=[x+c*y for x,y in zip(vv,ve)];new=add((1,new),(c,ae))
        v,aop=vv,new;actual=mat(actual,n['letters'][letter])
    assert actual==tuple(row['matrix'])
    branch=[(1,0,0,2),(1,3,0,2),(2,0,0,1)][row['new_branch']]
    for i,c in enumerate(v):states[(branch,i)]=states.get((branch,i),0)+c
    op=add((1,op),(1,right(aop,branch)))
    cert=cp((1,cert),(1,cr(error,branch)))
assert not any(states.values())
# λ(A−Atr) = −λ C R −λ PR S −λ C.
cert=cp((1,cert),(1,term(2,R,-1,1)),(1,term(0,S,-1,1)),(1,term(2,I,-1,1)))
alphas=[(1,0,0,2),(1,3,0,2),(2,0,0,1)]
H=add(*[(1,atom(a)) for a in alphas])
rels.append(H)
for ga in [S,mat(S,R),mat(mat(S,R),R)]:
    cert=cp((1,cert),(1,term(4,ga,-1)))
# Generator4 is H−lambda, handled separately when evaluating.
final={}
for (gi,m,deg),c in cert.items():
    if gi==3:
        final=cp((1,final),(c,{(j,mat(a,m),d+deg):v for (j,a,d),v in ducert.items()}))
    else:final=cp((1,final),(c,term(gi,m,deg=deg)))
value=evalcert(final)
for (gi,m,deg),c in final.items():
    if gi==4:
        tag=(m,deg+1);value[tag]=value.get(tag,F(0))-c
value={t:v for t,v in value.items() if v}
target={(m,1):v for m,v in A.items()}
for m,c in op.items():
    for a,v in right(A,m).items():
        tag=(a,0);target[tag]=target.get(tag,F(0))-c*v
target={t:v for t,v in target.items() if v}
assert value==target
expected={ (1,-1,0,2):F(1),(2,0,0,1):F(-1),(2,1,0,1):F(1),(2,2,0,1):F(-1)}
assert op==expected
out={'status':'PASS_EXACT_Q_LAMBDA_ORIGINAL_RIGHT_IDEAL',
     'generators':['PR','PS','SR-RS','unused','H2-lambda'],
     'terms':[{'generator':gi,'right_matrix':m,'lambda_power':d,'coefficient':str(c)}
              for (gi,m,d),c in sorted(final.items())],
     'A_operator':[[m,str(c)] for m,c in sorted(op.items())],
     'source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in [Path(__file__),source,base/'level27_continuation_geometry_hecke.py']}}
path=Path('/tmp/level27_continuation_geometry_certificate.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],len(final),'terms')
