"""Export all projective charts of the exact reduced leading/jet system."""
from pathlib import Path
import json,sys
eta=int(sys.argv[1]);suffix='_zero2' if 'zero2' in sys.argv else ''
prefix='level25_cusp_aux_oldgerm_' if 'old' in sys.argv else 'level25_cusp_aux_prime7_firstjet_'
data=json.loads(Path('/tmp/'+prefix+'reduced_'+str(eta)+suffix+'.json').read_text());cols=data['free'];assert len(cols)==2
for chart in range(2):
 polys=[]
 for row in data['rows']:
  terms=[]
  for j,p,q in row['terms']:
   if chart==1 and j==cols[0]:continue
   names=['x','y','z','w','a','b','c']
   term='('+q+')'+''.join('*'+names[i]+('^'+str(e) if e!=1 else '') for i,e in enumerate(p) if e)
   if chart==0 and j==cols[1]:term+='*u'
   terms.append(term)
  if terms:polys.append('+'.join(terms))
 text='SetSeed(1); Alarm(45);\nR<u,c,b,a,z,w,y,x,t>:=PolynomialRing(Rationals(),9,"grevlex");\n'
 text+='P:=[R|'+',\n'.join(polys+['t*x*y*z*w-1'])+'];\n'
 text+='print "BEGIN",#P; time I:=ideal<R|P>; time G:=GroebnerBasis(I); print "GB",#G; if #G lt 12 then G; else print "DIM",Dimension(I); E:=EliminationIdeal(I,{x,y}); print "XY",Basis(E); end if; quit;\n'
 path=Path('/tmp/'+prefix+'ideal_'+str(eta)+suffix+'_'+str(chart)+'.m');path.write_text(text);print(path)
