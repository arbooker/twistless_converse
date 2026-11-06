"""Exact N26 Taylor rows enlarged by a separate unramified eigenvalue at5."""
from pathlib import Path
import sys
qtarget=int(next(v[4:] for v in sys.argv if v.startswith('grid')))
src=Path(__file__).with_name('level26_jet_builder.py').read_text()
src=src.replace("K,x,y,z,a,b=field('x,y,z,a,b',QQ)","K,x,y,z,w,a,b=field('x,y,z,w,a,b',QQ)")
src=src.replace('N=26;Q=78','N=26;Q='+str(qtarget))
src=src.replace('V={2:x,3:y,13:z}','V={2:x,3:y,13:z,5:w}')
src=src.replace('(3,a),(13,K(bad13))','(3,a),(5,b),(13,K(bad13))')
src=src.replace('K.zero if p!=3 else V[p]**-2','K.zero if p in [2,13] else V[p]**-2')
exec(src)
