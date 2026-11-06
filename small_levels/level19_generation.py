"""Small exact Todd--Coxeter check for the level-19 generation step.

Uses the standard presentation PSL(2,Z)=<S,T | S^2=(S*T)^3=1>.
Every listed generator has determinant 1 and lower-left entry divisible
by 19, so the generated subgroup is contained in Gamma_0(19).
A completed Todd--Coxeter enumeration of index 20 proves equality,
since [PSL(2,Z):Gamma_0(19)]=20.
"""
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup, coset_enumeration_r

F, S, T = free_group('S,T')
G = FpGroup(F, [S**2, (S*T)**3])


def matrix_word(m):
    a,b,c,d = m
    result = F.identity
    while c:
        q = a//c
        result = result*T**q*S
        a,b,c,d = -c,-d,a-q*c,b-q*d
    assert a == d and a in (-1,1)
    return result*T**(b//a)


def mul(x,y):
    a,b,c,d=x; e,f,g,h=y
    return (a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h)


def power(m,n):
    if n < 0:
        a,b,c,d=m
        return power((d,-b,-c,a),-n)
    result=(1,0,0,1)
    for _ in range(n):
        result=mul(result,m)
    return result


def evaluate(word):
    result=(1,0,0,1)
    for name,n in word.array_form:
        m=(0,-1,1,0) if str(name)=='S' else (1,1,0,1)
        result=mul(result,power(m,n))
    return result


matrices = [(1,1,0,1), (1,0,19,1), (2,1,19,10),
            (5,-1,-19,4), (5,1,19,4)]
words=[]
for m in matrices:
    a,b,c,d=m
    assert a*d-b*c == 1 and c%19 == 0
    w=matrix_word(m)
    assert evaluate(w) in (m,tuple(-x for x in m))
    words.append(w)
    print(m,w)
C=coset_enumeration_r(G,words,max_cosets=2000)
assert C.is_complete()
C.compress()
assert C.n == 20
print('Index:',C.n)
print('Coset table, columns S,S^-1,T,T^-1:')
for i,row in enumerate(C.table):
    print(i,row)
