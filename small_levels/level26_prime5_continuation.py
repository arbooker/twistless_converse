"""Uniform leading continuation for the closed195 N26 subsystem."""
from pathlib import Path
exec(Path(__file__).with_name('level26_prime5_closed.py').read_text())
src=Path(__file__).with_name('level34_closed_continuation.py').read_text()
src=src[src.index("print('closedU'"):]
src=src.replace('powers[:3]','powers[:4]').replace('powers[3:]','powers[4:]')
src=src.replace('len(U)==90 and len(piv)==90','len(U)==195 and len(piv)==195')
src=src.replace('for q in [3,34]','for q in [3,5,78]').replace('bad17','bad13')
src=src.replace("'all_complex_lambda3':True","'all_complex_lambda3':True,'all_complex_lambda5':True")
src=src.replace("Path('/tmp/level34_closed_case.json')","Path('/tmp/level26_prime5_continuation_'+''.join('p' if v==1 else 'm' for v in (eta,bad2,bad13))+'.json')")
src=src.replace('N34_CLOSED_CONTINUATION_VERIFIED','N26_PRIME5_CONTINUATION_VERIFIED')
exec(src)
