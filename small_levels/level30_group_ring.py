"""Bounded exact group-ring exploration. Failure is not an obstruction proof.

All scalar values initially specialize lambda_2=lambda_3=lambda_5=-1,
eta_1=+1; good-prime lambda_7 is a generic finite-field probe.
A discovered relation still needs a symbolic/sign-uniform certificate.
"""
from math import gcd
from functools import reduce,lru_cache
from collections import deque
N=30
P=1000003

def norm(g):
 d=reduce(gcd,g)
 if next(t for t in g if t)<0:d=-d
 return tuple(t//d for t in g)
def mul(g,h):
 a,b,c,d=g;e,f,u,v=h
 return norm((a*e+b*u,a*f+b*v,c*e+d*u,c*f+d*v))
def inv(g):
 a,b,c,d=g;return norm((d,-b,-c,a))
def det(g):a,b,c,d=g;return a*d-b*c
I=(1,0,0,1);W=(0,1,-30,0);A=(16,1,30,2)
# Choose a rational generic basepoint metric to break W's fixed-point ties.
# Trace metric at i/sqrt(30) remains exact; lexicographic ties are harmless.
def quality(g):
 a,b,c,d=g
 return (30*a*a+900*b*b+c*c+30*d*d,30*det(g))
def better(g,h):
 u,v=quality(g);r,s=quality(h)
 return u*s<r*v or (u*s==r*v and g<h)
@lru_cache(maxsize=200000)
def canon(g):
 g=norm(g)
 for step in range(200):
  a,b,c,d=g;den=c*c+30*d*d
  ns={0}
  if den:
   num=-(a*c+30*b*d);q=num//den;ns.update([q-1,q,q+1,q+2])
  candidates=[norm((a+n*c,b+n*d,c,d)) for n in ns]
  candidates += [mul(h,g) for h in [W,A,inv(A)]]
  h=g
  for x in candidates:
   if better(x,h):h=x
  if h==g:return g
  g=h
 return g

def hecke(p):
 result=[((1,a,0,p),1) for a in range(p)]
 if N%p:result.append(((p,0,0,1),1))
 result.append((I,1 if N%p==0 else -13))
 return result

class Solver:
 def __init__(self):self.columns={};self.matrices=[];self.basis={};self.relations=0
 def col(self,g):
  g=canon(g)
  if g not in self.columns:self.columns[g]=len(self.matrices);self.matrices.append(g)
  return self.columns[g]
 def add(self,row):
  row={i:v%P for i,v in row.items() if v%P}
  self.relations+=1
  while row:
   j=max(row)
   if j not in self.basis:
    v=pow(row[j],-1,P);self.basis[j]={i:c*v%P for i,c in row.items()};return
   v=row[j]
   for i,c in self.basis[j].items():
    val=(row.get(i,0)-v*c)%P
    if val:row[i]=val
    else:row.pop(i,None)
 def reduce(self,row):
  for j in sorted(self.basis,reverse=True):
   if j not in row:continue
   v=row[j]
   for i,c in self.basis[j].items():
    val=(row.get(i,0)-v*c)%P
    if val:row[i]=val
    else:row.pop(i,None)
  return row
 def run(self,cap):
  targets=[self.col(I),self.col((-9,1,-30,3)),self.col((-5,1,-30,5))]
  for idx in range(cap):
   if idx>=len(self.matrices):break
   g=self.matrices[idx]
   for p in [2,3,5,7]:
    row={}
    for h,c in hecke(p):
     col=self.col(mul(h,g));row[col]=row.get(col,0)+c
    self.add(row)
   if idx%100==0:
    residues=[self.reduce({targets[0]:-1,targets[j]:1}) for j in [1,2]]
    print(idx,'columns',len(self.matrices),'basis',len(self.basis),'target lengths',[len(r) for r in residues],flush=True)
    if not any(residues):break
  return self
if __name__=='__main__':
 import sys
 Solver().run(int(sys.argv[1]) if len(sys.argv)>1 else 1000)
