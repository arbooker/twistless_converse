"""Exact monomial-only pole reduction on the N26 closed195 system."""
from pathlib import Path
wide=True
exec(Path(__file__).with_name('level26_prime5_closed.py').read_text())
src=Path(__file__).with_name('level34_finish_first_jet.py').read_text()
src=src[src.index('original = '):].replace('[0][0][3:]','[0][0][4:]')
src=src.replace('17**(n*pw[2]))','13**(n*pw[2]) * 5**(n*pw[3]))')
src=src.replace('bad17','bad13')
src=src.replace("'/tmp/level34_finish_rows_'","'/tmp/level26_prime5_rows_'")
src=src.replace("'free': free,","'free': free, 'kernels78': [[str(p[j]) for j in range(0,Q,5)] for p in kernels],")
src=src[:src.index('    for i, r in enumerate(rows[:20]):')] if 'probe' in sys.argv else src
exec(src)
