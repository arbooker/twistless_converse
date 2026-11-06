"""Exact complete-support closure for the prime5 enlarged N26 system."""
from pathlib import Path
import json
exec(Path(__file__).with_name('level26_prime5_builder.py').read_text())
assert Q==390
U=set(json.loads(Path(__file__).with_name('level26_prime5_support.json').read_text())['U'])
src=Path(__file__).with_name('level34_finish_grid_builder.py').read_text()
src=src[src.index('def closed(row,lab):'):]
src=src.replace('for q in [3,34]','for q in [3,5,78]')
exec(src)
