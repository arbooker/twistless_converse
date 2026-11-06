"""Tiny exact finite-quotient check for level36; no algebra package needed."""
from collections import deque
from pathlib import Path
import hashlib,json

def mul(a,b):
    return tuple(tuple(sum(x*y for x,y in zip(row,col)) for col in zip(*b)) for row in a)
def eye(n):return tuple(tuple(int(i==j) for j in range(n)) for i in range(n))
def power(a,n):
    v=eye(len(a))
    for _ in range(n):v=mul(v,a)
    return v
def neg(a):return tuple(tuple(-x for x in r) for r in a)
S=((0,-1),(1,0));T=((1,1),(0,1))
positiveS=((1,0,0),(0,0,1),(0,1,0))
positiveT=((0,1,0),(-1,1,0),(1,0,-1))
negativeS=neg(eye(2));negativeT=((0,1),(-1,1))
results={}
for name,rs,rt in [('positive',positiveS,positiveT),('negative_after_H_zero',negativeS,negativeT)]:
    n=len(rs)
    assert power(rs,2)==eye(n)
    assert power(mul(rs,rt),3)==eye(n)
    assert power(rt,3)==neg(eye(n))
    reps={eye(2):eye(n)};todo=deque([eye(2)])
    while todo:
        m=todo.popleft()
        for gen,rgen in [(S,rs),(T,rt)]:
            nxt=tuple(tuple(x%6 for x in row) for row in mul(m,gen))
            rep=mul(reps[m],rgen)
            if nxt in reps: assert reps[nxt]==rep
            else:reps[nxt]=rep;todo.append(nxt)
    assert len(reps)==144
    minus_identity=((5,0),(0,5))
    assert reps[minus_identity]==eye(n)
    results[name]={'SL2_mod6_elements':len(reps),'representation_image_size':len(set(reps.values())),
                   'Gamma6_invariant':True,'minus_identity_trivial':True,'T_cube':'-identity'}
out={'status':'PASS exact SL2(Z/6) factorization','cases':results,
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('level36_congruence_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
