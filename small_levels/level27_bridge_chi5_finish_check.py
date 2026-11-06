"""Independent exact audit of the chi5 defect expansion and elliptic finish.

Every state-table row has an explicit certificate in PR,PS,C,B+AU.
No root implementation is imported, no numerical/group search is used.
"""
from pathlib import Path
from document_provenance import source_sha256, recorded_document_provenance
from fractions import Fraction as F
from functools import reduce
from math import gcd
import hashlib,json
def canonical(v):
 vals=[F(x) for x in v];den=1
 for x in vals:den=den*x.denominator//gcd(den,x.denominator)
 ints=[int(x*den) for x in vals];common=reduce(gcd,ints)
 ints=[x//abs(common) for x in ints]
 if next(x for x in ints if x)<0:ints=[-x for x in ints]
 return tuple(ints)
def mat(a,b):
 return canonical([a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],
                   a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3]])
def inverse(a):return canonical([a[3],-a[1],-a[2],a[0]])
I=(1,0,0,1);R=(1,1,0,1);S=(1,0,3,1);r=inverse(R);s=inverse(S)
def add(*args):
 out={}
 for c,poly in args:
  for m,v in poly.items():out[m]=out.get(m,F(0))+F(c)*v
 return {m:v for m,v in out.items() if v}
def atom(m):return {canonical(m):F(1)}
def right(p,m):return add(*[(v,atom(mat(k,m))) for k,v in p.items()])
PR=add((1,atom(I)),(1,atom(R)),(1,atom(mat(R,R))))
PS=add((1,atom(I)),(1,atom(S)),(1,atom(mat(S,S))))
C=add((1,atom(mat(S,R))),(-1,atom(mat(R,S))))
A=add((1,atom(mat(mat(R,S),R))),(-1,atom(mat(mat(R,R),S))))
B=add((1,atom(mat(mat(S,S),R))),(-1,atom(mat(mat(S,R),S))))
U=mat(r,S);DU=add((1,B),(1,right(A,U)))
states=[I,R,S,mat(R,S)]
table={
 'R':[([0,1,0,0],{}),([-1,-1,0,0],{}),([0,0,0,1],{}),([0,0,-1,-1],atom(I))],
 'S':[([0,0,1,0],{}),([0,0,0,1],{}),([-1,0,-1,0],{}),([0,-1,0,-1],atom(U))],
 'r':[([-1,-1,0,0],{}),([1,0,0,0],{}),([0,0,-1,-1],atom(r)),([0,0,1,0],{})],
 's':[([-1,0,-1,0],{}),([0,-1,0,-1],atom(r)),([1,0,0,0],{}),([0,1,0,0],{})]}
Slast=add((1,right(PS,R)),(-1,right(C,S)),(-1,C),(-1,DU))
certificates={
 'R':[{},PR,C,right(PR,S)],
 'S':[{}, {},PS,Slast],
 'r':[right(PR,r),{},add((1,right(right(PR,S),r)),(1,right(C,r))),add((-1,right(C,r)))],
 's':[right(PS,s),right(Slast,s),{},{}]}
letters={'R':R,'S':S,'r':r,'s':s}
def apply_A(op):return add(*[(v,right(A,m)) for m,v in op.items()])
for letter in letters:
 for i,(vec,op) in enumerate(table[letter]):
  target=add((1,atom(mat(states[i],letters[letter]))),
             *[(-c,atom(m)) for c,m in zip(vec,states)],(-1,apply_A(op)))
  assert target==certificates[letter][i],(letter,i)
# Independently replay the two words using the now-certified state table.
def expand(word):
 v=[1,0,0,0];op={};actual=I
 for letter in word:
  coeff=[0,0,0,0];new=right(op,letters[letter])
  for c,(vec,err) in zip(v,table[letter]):
   coeff=[x+c*y for x,y in zip(coeff,vec)];new=add((1,new),(c,err))
  v,op=coeff,new;actual=mat(actual,letters[letter])
 return actual,v,op
gm,v,minus=expand('sRssr');gp,vp,plus=expand('RsRSR')
assert v==vp==[1,0,0,0]
assert gm==(5,-6,-9,11) and gp==(5,6,9,11)
assert minus=={(4,-5,-3,4):F(-1)}
assert plus=={(2,3,-3,-4):F(1)}
combined=add((1,right(minus,(5,6,0,5))),(1,right(plus,(5,-6,0,5))))
M=(10,3,-15,-2);N=(20,-1,-15,2)
assert combined=={M:F(1),N:F(-1)}
# Exact normalization from the unrescaled paired defect E1.
D=(1,0,0,3)
assert mat(mat(inverse(D),(5,-2,-27,11)),D)==gm
assert mat(mat(inverse(D),(5,2,27,11)),D)==gp
assert mat(mat(inverse(D),(5,2,0,5)),D)==(5,6,0,5)
assert mat(mat(inverse(D),(5,-2,0,5)),D)==(5,-6,0,5)
ell=mat(M,inverse(N));assert ell==(13,14,-12,-11)
det=ell[0]*ell[3]-ell[1]*ell[2];tr=ell[0]+ell[3]
assert det==25 and tr==2 and F(tr*tr,det)==F(4,25)
here=Path(__file__).resolve().parent
files=[Path(__file__),here/'level27_bridge_chi5_finish.tex',here/'level27_root_chi5_defect.py',
       here/'level27_defects_single_obstruction.tex',here/'level27_bridge_chi5_reduction.tex']
out={'status':'PASS_INDEPENDENT_STATE_CERTIFICATES_NORMALIZATION_AND_CONDITIONAL_FINISH',
 'state_certificates':16,'paired_operator':[M,N],'elliptic_matrix_projective':ell,
 'trace_squared_over_determinant':'4/25','chi5_FE_proved':False,
 'sources':{p.name:source_sha256(p) for p in files}}
out['document_hash_provenance'] = recorded_document_provenance(); (here/'level27_bridge_chi5_finish_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'])
