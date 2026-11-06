"""Bounded sequential generation of one N26 prime5 sign case."""
from pathlib import Path
import subprocess,sys
root=Path(__file__).resolve().parent
code=sys.argv[1];assert len(code)==3 and set(code)<=set('mp')
signs=['-1' if c=='m' else '1' for c in code]
for name,args in [('first_jet',signs+['grid390','probe']),('continuation',signs+['grid390'])]:
 subprocess.run([sys.executable,'-B',str(root/('level26_prime5_'+name+'.py')),*args],check=True,timeout=55)
print('N26_PRIME5_ROWS_AND_CONTINUATION_VERIFIED',code,flush=True)
