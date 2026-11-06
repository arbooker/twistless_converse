"""Check the level-21 identities and emit the exact Magma subgroup input.

Run from any directory. Use --output PATH to choose the generated input's
location; the default remains the system temporary directory.
"""
import argparse
import tempfile
import sympy as s
from pathlib import Path
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path,
                    default=Path(tempfile.gettempdir()) / 'level21_22_modularity_generic.m')
args = parser.parse_args()
source_dir = Path(__file__).resolve().parent
exec((source_dir / 'level21_22_modularity_chi5.py').read_text())
P=s.Matrix([[3,1],[-21,-6]]); Q=s.Matrix([[3,-1],[21,-6]])
def eq(X,Y):
 assert X==Y or X==-Y,(X,Y)
eq(P*P/3,A.inv())
eq(P*t(-1)*Q.inv(),Cmat*E.inv()*U.inv())
eq(M0*P,A*P*M1)
eq(M2*P,Cmat.inv()*P*M0)
eq(M1*P,E*Cmat.inv()*P*t(-1)*M2)
print('P identities pass')
exec((source_dir / 'level19_generation.py').read_text().split('matrices =')[0])
base=[t(1),U,E,Cmat,D,A,BB]
reps=[s.eye(2),P,w(21),P*w(21)]
mats=[]
for rep in reps:
 for g in base:
  h=rep*g*rep.inv()
  assert all(z.q==1 for z in h) and h.det()==1
  m=tuple(map(int,h)); assert m[2]%21==0
  if m not in mats:mats.append(m)
words=[]
for m in mats:
 wd=matrix_word(m); assert evaluate(wd) in (m,tuple(-x for x in m))
 words.append(str(wd).replace('**','^'))
args.output.write_text('G<S,T>:=Group<S,T|S^2,(S*T)^3>;\nH:=sub<G|'+','.join(words)+'>;\ni:=Index(G,H:CosetLimit:=50000,TimeLimit:=10); print i; assert i eq 32; quit;\n')
print('Magma file',len(mats))
