"""Exact matrix/Schreier certificate for <T,U7,E7>=Gamma0(7) in PSL2Z.
The independently executable Magma index check is the companion .m file.
"""
from itertools import product
def mul(g,h):
    a,b,c,d=g;e,f,q,r=h
    return canon((a*e+b*q,a*f+b*r,c*e+d*q,c*f+d*r))
def canon(g):
    return tuple(-v for v in g) if next(v for v in g if v)<0 else tuple(g)
def inv(g):
    a,b,c,d=g
    return canon((d,-b,-c,a))
def power(g,n):
    if n<0:return power(inv(g),-n)
    h=I
    for _ in range(n):h=mul(h,g)
    return h
I=(1,0,0,1);S=(0,1,-1,0);T=(1,1,0,1);U=(1,0,7,1);E=(2,-1,-7,4)
assert mul(mul(S,power(T,-7)),S)==U
assert mul(mul(mul(mul(mul(S,power(T,3)),S),power(T,-2)),S),power(T,-1))==E
gens={'T':T,'U':U,'E':E,'t':inv(T),'u':inv(U),'e':inv(E)}
def evaluate(word):
    out=I
    for letter in word:out=mul(out,gens[letter])
    return out
def cusp_coset(g):
    c,d=g[2]%7,g[3]%7
    return None if c==0 else d*pow(c,-1,7)%7
reps={None:I,**{j:mul(S,power(T,j)) for j in range(7)}}
assert len({cusp_coset(r) for r in reps.values()})==8
# Meet-in-the-middle words of length at most eight suffice for all
# Reidemeister--Schreier generators from this explicit transversal.
words={I:''};front={I:''}
for depth in range(4):
    nxt={}
    for g,w in front.items():
        for letter,h in gens.items():
            gh=mul(g,h)
            if gh not in words:nxt.setdefault(gh,w+letter)
    words.update(nxt);front=nxt
def find_word(target):
    if target in words:return words[target]
    for g,w in words.items():
        h=mul(inv(g),target)
        if h in words:return w+words[h]
    raise AssertionError(('word search failed',target))
schreier=[]
for label,r in reps.items():
    for letter,g in [('S',S),('T',T)]:
        rg=mul(r,g);new=cusp_coset(rg);h=mul(rg,inv(reps[new]))
        assert h[0]*h[3]-h[1]*h[2]==1 and h[2]%7==0
        word=find_word(h)
        assert evaluate(word)==h
        schreier.append((label,letter,new,h,word))
        print('SCHREIER',label,letter,new,h,word or '1',flush=True)
assert len(schreier)==16
print('EXPLICIT_SCHREIER_GENERATION_INDEX_8_VERIFIED',flush=True)
