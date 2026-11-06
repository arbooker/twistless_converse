"""Exact raw-row and Taylor-source transport for both bad-13 signs.

No Groebner calculation or residue/pole-order assumption is made here.
Outputs only a small audit JSON beside this source; no build cache.
"""
from pathlib import Path
from document_provenance import source_sha256, recorded_document_provenance
from fractions import Fraction
from math import factorial
from collections import Counter
import contextlib, hashlib, io, json, signal, sys, time

signal.alarm(120)
base = Path(__file__).parent
start = time.monotonic()

def build(eta, bad2, bad13):
    sys.argv = [str(__file__), str(eta), str(bad2), str(bad13), 'grid780']
    env = {'__file__': str(base/'level26_prime5_wide_closed.py')}
    with contextlib.redirect_stdout(io.StringIO()):
        exec((base/'level26_prime5_wide_closed.py').read_text(), env)
    return env

def parity13(n):
    n = abs(n); count = 0
    while n % 13 == 0:
        n //= 13; count += 1
    return -1 if count % 2 else 1

def key(lab, transport):
    if transport and lab[0] == 'g':
        _, A, B, C, D, mu, j = lab
        return ('g', A, B, C, D, mu*parity13(A*D-B*C), j)
    return lab

def source(env, lab, order):
    """Exact pre-elimination source from the original higher-Taylor code."""
    K, Q = env['K'], env['Q']
    mon, lcm, gcd = env['mon'], env['lcm'], env['gcd']
    if lab[0] == 'g':
        _, A, B, C, D, mu, j = lab
        den, det = C*j+D*Q, A*D-B*C
        dest = Q*(A*j+B*Q)//den % Q
        leading = mu*mon(Fraction(den*den, det*Q*Q))
        slope = K(Fraction(C*den, det*Q))
        return {dest: leading*slope**order/K(factorial(order))}
    if lab[0] == 'F':
        _, q, t = lab; ell = lcm(26, q*q)
        dest = -(Q*Q//ell)//t
        leading = (env['eta']*(-env['bad2'] if q % 2 == 0 else 1)
                   *(-env['bad13'] if q % 13 == 0 else 1)
                   *mon(Fraction(ell*t*t, Q*Q)))
        value = leading*K(Fraction(ell*t, Q))**order/K(factorial(order))
        return {(a0*(Q//q)+dest) % Q: value for a0 in range(q) if gcd(a0,q)==1}
    return {}

results = []
for eta in [-1,1]:
    for bad2 in [-1,1]:
        positive, negative = build(eta,bad2,1), build(-eta,bad2,-1)
        K = positive['K']
        cache = {}
        def flip(v):
            if v not in cache:
                def pol(p):
                    return K(K.ring.from_dict({e:c*(-1)**e[2] for e,c in p.terms()}))
                cache[v] = pol(v.numer)/pol(v.denom)
            return cache[v]
        def clean(row, transport=False):
            return tuple(sorted((j,flip(v) if transport else v) for j,v in row.items() if v))
        assert positive['U'] == negative['U']
        neg = Counter((key(lab,False),clean(row)) for row,lab in negative['R'])
        pos = Counter((key(lab,True),clean(row,True)) for row,lab in positive['R'])
        assert pos == neg
        for order in [1,2]:
            pos = Counter((key(lab,True),clean(source(positive,lab,order),True))
                          for row,lab in positive['R'])
            neg = Counter((key(lab,False),clean(source(negative,lab,order)))
                          for row,lab in negative['R'])
            assert pos == neg
        def shift(v, n):
            def pol(p):
                return K(K.ring.from_dict({e:c/(2**(n*e[0])*3**(n*e[1])
                                              *13**(n*e[2])*5**(n*e[3]))
                                          for e,c in p.terms()}))
            return pol(v.numer)/pol(v.denom)
        for v in list(cache):
            for n in [1,2]:
                assert flip(shift(v,n)) == shift(flip(v),n)
        # Every higher source uses the same sign-covariant leading scalar
        # and a sign-independent rational slope; orders 1,2 are the certificate.
        results.append({'positive_signs':[eta,bad2,1],
                        'negative_signs':[-eta,bad2,-1],
                        'coordinates':len(positive['U']), 'rows':len(positive['R']),
                        'row_types':dict(Counter(lab[0] for row,lab in positive['R'])),
                        'leading':'PASS','source_orders_1_2':'PASS',
                        'shift_commutation_1_2':'PASS'})
        print('PASS',results[-1],flush=True)

names = ['level26_positive_repair_check.py','level26_positive_repair_proof.tex',
         'level26_jet_builder.py',
         'level26_prime5_builder.py','level26_prime5_wide_closed.py',
         'level26_prime5_wide_support.json','level34_finish_grid_builder.py',
         'level26_finish_higher.py','level26_negative_poles_backend.m']
out = {'status':'PASS exact sign transport of all raw closed rows and Taylor sources',
       'map':'(eta,sigma2,sigma13,z) -> (-eta,sigma2,-sigma13,-z)',
       'cases':results,'elapsed_seconds':time.monotonic()-start,
       'source_sha256':{n:source_sha256(base/n) for n in names}}
out['document_hash_provenance'] = recorded_document_provenance(); (base/'level26_positive_repair_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print('ALL_FOUR_POSITIVE_CASES_TRANSPORTED_EXACTLY',flush=True)
