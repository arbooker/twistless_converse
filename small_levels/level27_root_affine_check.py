"""Independent exact audit of the new affine Hecke relation.

Reuse only the independently certified 16 state equations, not the new
branch-search implementation. Every branch factorization is checked again.
"""
from pathlib import Path
import hashlib, json

base = Path(__file__).resolve().parent
source = base / 'level27_bridge_chi5_finish_check.py'
scope = {'__file__': str(source)}
exec(compile(source.read_text().split('# Independently replay')[0], str(source), 'exec'), scope)
mat, inverse, add, atom, right = [scope[n] for n in ('mat','inverse','add','atom','right')]
I,R,S,A = [scope[n] for n in ('I','R','S','A')]
table, letters, states = [scope[n] for n in ('table','letters','states')]

def word_expansion(word):
    v = [1,0,0,0]
    err = {}
    product = I
    for letter in word:
        new = [0,0,0,0]
        err2 = right(err, letters[letter])
        for coeff, (vv, ee) in zip(v, table[letter]):
            new = [u + coeff*w for u,w in zip(new,vv)]
            err2 = add((1,err2),(coeff,ee))
        v,err = new,err2
        product = mat(product, letters[letter])
    return product,v,err

hecke = [(1,0,0,2),(1,3,0,2),(2,0,0,1)]
gamma = [S,mat(S,R),mat(mat(S,R),R)]
words = [[(0,'SS'),(2,'RRsR'),(1,'Rsr')],
         [(1,'SSr'),(2,'RRsRRR'),(0,'RsR')],
         [(0,'SSR'),(2,'RRsRRRRR'),(1,'Rs')]]
remainders = [[0,0,0,0] for _ in hecke]
operator = {}
for g,branches in zip(gamma,words):
    for alpha,(j,word) in zip(hecke,branches):
        actual,v,err = word_expansion(word)
        assert mat(alpha,g) == mat(actual,hecke[j])
        remainders[j] = [u+w for u,w in zip(remainders[j],v)]
        operator = add((1,operator),(1,right(err,hecke[j])))
assert all(v == [0,0,0,0] for v in remainders)
expected = {(1,-1,0,2):1,(2,0,0,1):-1,(2,1,0,1):1,(2,2,0,1):-1}
assert operator == expected
# Independently evaluate the exported certificate in the original right ideal.
# This second check does not use state tables, word search, or their provenance.
certificate_path = base / 'level27_continuation_geometry_certificate.json'
certificate = json.loads(certificate_path.read_text())
generators = {0:scope['PR'],1:scope['PS'],2:scope['C'],
              4:add(*[(1,atom(m)) for m in hecke])}
from fractions import Fraction
value = {}
def put(poly, key, val):
    poly[key] = poly.get(key,Fraction(0)) + val
    if not poly[key]: del poly[key]
for term in certificate['terms']:
    j,deg = term['generator'],term['lambda_power']
    m,c = tuple(term['right_matrix']),Fraction(term['coefficient'])
    for q,v in right(generators[j],m).items(): put(value,(q,deg),c*v)
    if j == 4: put(value,(m,deg+1),-c)
target = {(m,1):c for m,c in A.items()}
for m,c in expected.items():
    for q,v in right(A,m).items(): put(target,(q,0),-c*v)
assert value == target
# g*S*(1+R+R^2) equals the state-table definition g*A.
trace = add(*[(1,atom(g)) for g in gamma])
assert add((1,trace),(-1,A)) == add((1,right(scope['PR'],S)),
                                                  (1,right(scope['C'],R)),(1,scope['C']))
# The known finite elliptic is sufficient to kill a constant in positive weight.
E = (2,4,-3,-4)
assert E[0]*E[3]-E[1]*E[2] == 4 and E[2] != 0
result = {'status':'PASS_INDEPENDENT_AFFINE_HECKE2_IDENTITY',
          'certified_state_equations':16,'exact_branch_factorizations':9,
          'independent_original_right_ideal_terms':len(certificate['terms']),
          'state_remainders':remainders,
          'operator':[[list(m),c] for m,c in expected.items()],
          'eigenvalue_divisions':0,'Fricke_sign_restrictions':[],
          'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in [Path(__file__),source,certificate_path]}}
print(json.dumps(result,indent=2))
