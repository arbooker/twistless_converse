"""Exact expansion of the paired chi5 defect in the single obstruction A.

Uses the proved four-state action with its A error terms. It does not
claim the resulting obstruction operator vanishes.
"""
import json
from fractions import Fraction
from functools import reduce
from math import gcd

def norm(m):
    d=reduce(gcd,m);m=tuple(x//abs(d) for x in m)
    return tuple(-x for x in m) if next(x for x in m if x)<0 else m
def mul(m,n):
    a,b,c,d=m;e,f,g,h=n
    return norm((a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h))
def inv(m):
    a,b,c,d=m;return norm((d,-b,-c,a))
I=(1,0,0,1);R=(1,1,0,1);S=(1,0,3,1)
gens={'R':R,'r':inv(R),'S':S,'s':inv(S)}
U=mul(inv(R),S);E=(2,4,-3,-4);J=norm((-3,-4,3,3))
def accum(op,m,c):
    op[m]=op.get(m,0)+c
    if not op[m]:del op[m]
def right(op,m):
    out={}
    for a,c in op.items():accum(out,mul(a,m),c)
    return out

# Image of each basis vector, then the additional A coefficient operator.
actions={
 'R': [([0,1,0,0],{}),([-1,-1,0,0],{}),([0,0,0,1],{}),([0,0,-1,-1],{I:1})],
 'S': [([0,0,1,0],{}),([0,0,0,1],{}),([-1,0,-1,0],{}),([0,-1,0,-1],{U:1})],
 'r': [([-1,-1,0,0],{}),([1,0,0,0],{}),([0,0,-1,-1],{inv(R):1}),([0,0,1,0],{})],
 's': [([-1,0,-1,0],{}),([0,-1,0,-1],{inv(R):1}),([1,0,0,0],{}),([0,1,0,0],{})]
}
def expand(word):
    v=[1,0,0,0];op={};matrix=I
    for letter in word:
        op=right(op,gens[letter]);n=[0]*4
        for c,(vv,oo) in zip(v,actions[letter]):
            for j in range(4):n[j]+=c*vv[j]
            for m,b in oo.items():accum(op,m,c*b)
        v=n;matrix=mul(matrix,gens[letter])
    return matrix,v,op

words=['sRssr','RsRSR']
expected=[(5,-6,-9,11),(5,6,9,11)]
translations=[(5,6,0,5),(5,-6,0,5)]
combined={};expansions=[]
for word,expect,tr in zip(words,expected,translations):
    matrix,v,op=expand(word)
    assert matrix==norm(expect) and v==[1,0,0,0]
    expansions.append({'word':word,'matrix':matrix,'A_operator':[{'matrix':m,'coefficient':c} for m,c in sorted(op.items())]})
    for m,c in right(op,tr).items():accum(combined,m,c)

def c6_reduce(op,eta):
    sym=[];ep=I
    for i in range(3):
        sym += [(ep,1),(mul(ep,J),-eta)]
        ep=mul(ep,E)
    out={}
    for m,c in op.items():
        mm,sgn=min((mul(h,m),sgn) for h,sgn in sym)
        accum(out,mm,c*sgn)
    return out
M=(10,3,-15,-2);N=(20,-1,-15,2)
assert combined=={M:1,N:-1}
elliptic=mul(M,inv(N))
assert elliptic==(13,14,-12,-11)
det=lambda m:m[0]*m[3]-m[1]*m[2]
trace=elliptic[0]+elliptic[3]
assert det(elliptic)==25 and trace==2
assert Fraction(trace*trace,det(elliptic))==Fraction(4,25)
assert c6_reduce(combined,1)=={(0,5,-15,-3):1,(0,10,-30,-9):-1}
assert c6_reduce(combined,-1)=={(0,5,-15,-3):-1,(0,10,-30,-9):1}
print(json.dumps({'status':'PASS: exact conditional chi5-to-converse reduction; chi5 identity remains unproved',
                  'expansions':expansions,
                  'infinite_elliptic':{'matrix':elliptic,'determinant':det(elliptic),'trace':trace,'normalized_trace':'2/5'},
                  'paired_operator':[{'matrix':m,'coefficient':c} for m,c in sorted(combined.items())],
                  'C6_reductions':{eta:[{'matrix':m,'coefficient':c} for m,c in sorted(c6_reduce(combined,eta).items())] for eta in (1,-1)}},indent=2))
