"""Exact leading-matrix rank at a fixed positive even weight; no uniform claim."""
import sys,json
from pathlib import Path
from sympy import symbols,sympify,cancel,groebner
x,y,z,w,a,b,t=symbols('x y z w a b t')
code=sys.argv[1];m=int(sys.argv[2]);assert m>=1
d=json.loads(Path('/tmp/level26_prime5_rows_780_'+code+'.json').read_text())
rows=[[cancel(sympify(v).subs({x:2**m,y:3**m,z:13**m,w:5**m})) for v in r] for r in d['lead']]
out=[]
for chart in [0,1]:
 polys=list(set(cancel(r[1] if chart==0 else r[0]+t*r[1]).as_numer_denom()[0] for r in rows))
 G=groebner(polys,t,a,b,method='f5b')
 print('weight',2*m,'signs',code,'chart',chart,'GB',list(G),flush=True)
 out.append([str(v) for v in G])
Path('/tmp/level26_prime5_weightk_'+code+'_'+str(m)+'.json').write_text(json.dumps({'signs':d['signs'],'k':2*m,'chart_bases':out},indent=2)+'\n')
