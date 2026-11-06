"""Exact Q1050 quotient first-jet relations, using only monomial elimination.
No pole-order assumption is made at lower points: zero-row identities
annihilate their complete meromorphic germs. Nonzero residual rows
need further germ-syzygy elimination before becoming first-jet constraints.
"""
from pathlib import Path
import sys,time,json,signal
signal.alarm(300)
jet_suffix="_zero2" if "zero2" in sys.argv else ("_nonzero2" if "nonzero2" in sys.argv else "")
base=Path(__file__).parent
aux_source=(base/'level25_cusp_aux_prime7_symbolic.py').read_text()
aux_cut=aux_source.index("\nif 'old150' in sys.argv:\n    assert not R")
sys.argv.append('old150');exec(aux_source[:aux_cut]);assert not R
aux_gauges=list(free)
original=[(dict(row),lab) for row,lab in original if lab[0]!='old150']
original += [({j:K.one},('gauge',j)) for j in aux_gauges]
R=[(dict(row),i) for i,(row,lab) in enumerate(original)]
jet_source=(base/'level25_finish_firstjet.py').read_text()
jet_source=jet_source[jet_source.index('def safe(v):'):jet_source.index('constraints=[]')]
jet_source=jet_source.replace('[3:]','[4:]').replace('5**pw[2])','5**pw[2]*7**pw[3])').replace('>60','>180')
jet_source=jet_source.replace('operations.append((rid,val,updates));R=new', 'operations.append((rid,val,updates));R=new\n if len(piv)%100==0:print("LOWER_PIVOTS",len(piv),round(time.time()-st,1),flush=True)')
if 'nonzero2' in sys.argv:jet_source=jet_source.replace('[4:]','[5:]')
jet_source=jet_source.replace('  bvec[rid]/=shift(val)', '  if not bvec[rid]:continue\n  bvec[rid]/=shift(val)')
exec(jet_source)
constraints=[]
for row,rid in R:constraints.append(({i:row[c] for i,c in enumerate(free) if c in row},('lead',original[rid][1])))
for rid in zeroids:
 v={t:sources[t][rid] for t in range(len(free)) if sources[t][rid]}
 if v:constraints.append((v,('jet',original[rid][1])))
for j in range(0,Q,Q//5):
 v={t:pole[j] for t,pole in enumerate(poles) if pole[j]}
 if v:constraints.append((v,('old5',j)))
print('CONSTRAINTS',len(constraints),'FREE',free,flush=True)
# Export before further row reduction; exact terms preserve all parameters.
def encode(v):return {'num':[(list(p),str(q)) for p,q in v.numer.terms()],'den':[(list(p),str(q)) for p,q in v.denom.terms()]}
data={'eta':eta,'free':free,'rows':[{'lab':lab,'row':{str(i):encode(v) for i,v in row.items()}} for row,lab in constraints]}
Path('/tmp/level25_cusp_aux_prime7_firstjet_'+str(eta)+jet_suffix+'.json').write_text(json.dumps(data))
# Each raw zero-row compatibility is legitimate; a nontrivial generic rank
# is deliberately not reported as an all-parameter proof.
print('FIRSTJET_EXPORTED',flush=True)
