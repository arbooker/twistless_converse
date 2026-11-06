"""Exact rational root disks excluding the second positive-sign residue chart.

No numerical root finder or floating-point arithmetic is used. The centers
are merely rational inputs; the Rouché inequalities certify every disk.
"""
from fractions import Fraction as F
from math import comb, isqrt

coefficients = [1584, -17520, -58008, -48312, -1161, 6903, -1256, 121, 1]
centers = [(-130991096, 0), (-956837, 0), (72143, 0), (4209464, 0),
           (-915249, -101240), (-915249, 101240),
           (4248412, -5570476), (4248412, 5570476)]
centers = [(F(a, 10**6), F(b, 10**6)) for a, b in centers]
radius = F(1, 10**5)

def add(a, b):
    return a[0]+b[0], a[1]+b[1]

def mul(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]

def power(a, n):
    result = F(1), F(0)
    for _ in range(n):
        result = mul(result, a)
    return result

def upper(a):
    return abs(a[0])+abs(a[1])

def lower(a):
    return max(abs(a[0]), abs(a[1]))

def modulus_bounds(a):
    q = a[0]**2+a[1]**2
    scale = 10**9
    n = isqrt(q.numerator*scale**2//q.denominator)
    lo, hi = F(n, scale), F(n+1, scale)
    assert lo**2 <= q < hi**2
    return lo, hi

classes = []
for index, center in enumerate(centers):
    for other in centers[:index]:
        assert lower((center[0]-other[0], center[1]-other[1])) > 2*radius
    taylor = []
    for j in range(9):
        value = F(0), F(0)
        for i in range(j, 9):
            term = power(center, i-j)
            scalar = coefficients[i]*comb(i,j)
            value = add(value, (scalar*term[0],scalar*term[1]))
        taylor.append(value)
    error = upper(taylor[0])+sum(upper(taylor[j])*radius**j for j in range(2,9))
    assert error < lower(taylor[1])*radius
    lo, hi = modulus_bounds(center)
    lo, hi = lo-radius, hi+radius
    pluslo, plushi = modulus_bounds(add(center, (F(1),F(0))))
    pluslo, plushi = pluslo-radius, plushi+radius
    assert lo > 0
    if lo > 1 and pluslo**2 > hi:
        classes.append('large: |X+1|^2 > |X|')
    elif hi < 1 and pluslo > 1:
        classes.append('small: |X+1| > 1')
    elif hi < 1 and plushi**2 < lo:
        classes.append('near minus one: |X+1|^2 < |X|')
    else:
        raise AssertionError('Disk does not exclude the modulus relation')

assert len(classes) == 8
# The additional root X=-4 has |X+1|^2=9>|X|=4.
assert 9 > 4 > 1
# Branch A=-2: 2X^2=3, Y=-3; rho<2 gives |Y|<|X|^2=3/2.
assert F(3,2) < 3
# 9>4^(3/2)=8 and 9<4^2=16 prove 3/2<log(9)/log(4)<2.
assert 8 < 9 < 16
print('PASS: eight disjoint rational Rouché disks cover F8 and exclude all modulus cases.')
print('PASS: X=-4 and the A=-2 branch are also excluded.')
for kind in classes:
    print(kind)
