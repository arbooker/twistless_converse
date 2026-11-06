"""Independent exact Hecke5 witness for collapse of the negative extension."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json

def mul(a,b):return tuple(tuple(sum(x*y for x,y in zip(row,col)) for col in zip(*b)) for row in a)
def eye(n):return tuple(tuple(int(i==j) for j in range(n)) for i in range(n))
def det(a):return a[0][0]*a[1][1]-a[0][1]*a[1][0]
def inv(a):
    d=det(a)
    return ((Q(a[1][1],d),Q(-a[0][1],d)),(Q(-a[1][0],d),Q(a[0][0],d)))
def power(a,n):
    out=eye(len(a))
    for _ in range(n):out=mul(out,a)
    return out
S=((0,-1),(1,0));T=((1,1),(0,1));U2=((1,0),(2,1))
rs=((-1,0,0),(0,0,1),(0,1,0));rt=((0,1,0),(-1,1,0),(1,0,1))
assert power(rt,6)==eye(3) and power(rs,2)==eye(3)
assert power(mul(rs,rt),3)==eye(3)

def representation(m):
    """Euclidean left reduction M=T^q S M_next; -I acts trivially."""
    assert det(m)==1
    rep=eye(3);wordmat=eye(2);a,b=m[0];c,d=m[1]
    while c:
        q=a//c
        a,b,c,d=c,d,q*c-a,q*d-b
        rep=mul(rep,mul(power(rt,q%6),rs))
        wordmat=mul(wordmat,mul(((1,q),(0,1)),S))
    assert a==d and a in [-1,1]
    assert mul(wordmat,((a,b),(0,d)))==m
    return mul(rep,power(rt,(b//a)%6))

gamma=((11,30),(-150,-409))
def period(m):
    assert all(Q(x).denominator==1 for row in m for x in row)
    m=tuple(tuple(int(x) for x in row) for row in m)
    assert any(all((m[i][j]-eps*int(i==j))%6==0 for i in range(2) for j in range(2))
               for eps in [-1,1])
    r=representation(m)
    assert r[0][0]==1 and r[0][1]==r[0][2]
    return r[0][1]
c=period(gamma)
branches=[((1,6*j),(0,5)) for j in range(5)]+[((5,0),(0,1))]
conjugates=[mul(mul(a,gamma),inv(a)) for a in branches]
cs=[period(m) for m in conjugates]
assert c==-2 and cs==[0,-4,2,-2,2,2]
assert all(mul(a,gamma)==mul(m,a) for a,m in zip(branches,conjugates))
out={'status':'PASS exact Hecke5 witness','gamma':[[int(x) for x in row] for row in gamma],
     'representation_method':'Exact Euclidean S,T decomposition of each matrix',
     'period_gamma':c,'periods_finite_branches':cs[:5],'period_infinite_branch':cs[5],
     'conjugates':[[[int(x) for x in row] for row in m] for m in conjugates],
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('level36_hecke_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
