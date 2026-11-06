"""Independent exact checker for the full zero-eigenvalue level-21 proof.

Only integer matrix products and rational arithmetic are used. The search
code, folded graph, and any negative membership answers are unnecessary.
A signed power word certifies each claimed subgroup membership explicitly.
"""
from fractions import Fraction as Q
from functools import reduce
from math import gcd
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
DATA=json.loads((ROOT/'level21_22_modularity_zero21_closure.json').read_text())
WORDS=json.loads((ROOT/'level21_22_modularity_zero21_words.json').read_text())
I=(1,0,0,1)
def norm(g):
    divisor=reduce(gcd,g)
    g=tuple(x//abs(divisor) for x in g)
    return tuple(-x for x in g) if next(x for x in g if x)<0 else g

def rawmul(x,y):
    a,b,c,d=x;e,f,g,h=y
    return (a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h)

def mul(x,y):return norm(rawmul(x,y))
def inv(g):a,b,c,d=g;return norm((d,-b,-c,a))
def det(g):a,b,c,d=g;return a*d-b*c
def power(g,n):
    if n<0:return power(inv(g),-n)
    ans=I
    for _ in range(n):ans=mul(ans,g)
    return ans

def checkword(entry,known):
    ans=I
    for index,exponent in entry['word']:
        assert 1<=index<=len(known) and exponent!=0
        ans=mul(ans,power(known[index-1],exponent))
    assert ans==norm(tuple(entry['target'])),entry

T=(1,1,0,1);U=(1,0,21,1);E=(2,-1,-21,11)
C=(5,-2,-42,17);D=(5,2,42,17)
P=(3,1,-21,-6);W=(0,-1,21,0)
Kplus=(43,6,-294,-41);Kminus=(85,24,-294,-83)
assert mul(mul(P,power(T,2)),inv(P))==Kplus
assert mul(mul(inv(P),power(T,2)),P)==Kminus
base=[T,U,E,C,D,Kplus,Kminus]
known=base+[mul(mul(W,g),inv(W)) for g in base]
count=0
for stage,item in enumerate(DATA['zero']+[DATA['five']]):
    p=2 if stage<4 else 5
    matrices=[(p,0,0,1)]+[(1,j,0,p) for j in range(p)]
    B=tuple(item['B']);new=tuple(item['new'])
    assert det(B)==det(new)==1 and B[2]%21==new[2]%21==0
    assert sorted(i for i,j,g in item['branches'])==list(range(p+1))
    assert sorted(j for i,j,g in item['branches'])==list(range(p+1))
    required=[]
    for i,j,g in item['branches']:
        g=tuple(g)
        assert det(g)==1 and g[2]%21==0
        assert mul(matrices[i],B)==mul(g,matrices[j])
        if g!=new:required.append(norm(g))
    assert len(required)==p
    if p==5:required.append(norm(B))
    entries=[entry for entry in WORDS if entry['stage']==stage]
    assert sorted(norm(tuple(entry['target'])) for entry in entries)==sorted(required)
    for entry in entries:checkword(entry,known);count+=1
    known.extend([new,mul(mul(W,new),inv(W))])
    assert all(det(g)==1 and g[2]%21==0 for g in known)
    print('PASS stage',stage+1,'prime',p,'prior-memberships',len(entries))
last=[entry for entry in WORDS if entry['stage']==5]
assert len(last)==1
checkword(last[0],known);count+=1
J=mul(mul(P,mul(T,U)),inv(P))
assert J==norm(tuple(DATA['J']))==norm(tuple(last[0]['target']))
# Rational defect stabilizer and final infinite elliptic matrix.
t=lambda r:(1,Q(r),0,1)
Pinverse=tuple(Q(x,det(P)) for x in (P[3],-P[1],-P[2],P[0]))
K=rawmul(rawmul(Pinverse,t(Q(2,3))),P)
assert K==(29,8,-98,-27)
M=rawmul(rawmul(rawmul(T,U),K),t(Q(-4,3)))
assert M==(540,-571,511,Q(-1621,3))
assert det(M)==1 and M[0]+M[3]==Q(-1,3)
assert count==15
print('PASS: 15 explicit prior-generator words; all 18 Hecke branches; final trace -1/3')
