"""Finite-field scouting only: enlarged leading and first-Taylor ranks."""
from pathlib import Path
exec(Path(__file__).with_name('level26_prime5_builder.py').read_text())
src=Path(__file__).with_name('level34_finish_wide_probe.py').read_text()
src=src[src.index('prime = 1009'):].replace('point = [2,3,17,5,7]','point = [2,3,13,5,7,11]')
src=src.replace("'/tmp/level34_finish_grid_'","'/tmp/level26_prime5_grid_'")
exec(src)
