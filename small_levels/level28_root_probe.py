"""Exploratory enlarged Q84 leading/first-jet elimination; no proof claim."""
from pathlib import Path
base=Path(__file__).parent
source=(base/'level28_pole_reduction.py').read_text()
source=source.replace("exec(Path(__file__).with_name('level28_jet_builder.py').read_text())",
 "exec((base/'level28_jet_builder.py').read_text().replace('N=28;Q=42','N=28;Q=84'))")
source=source.replace('assert len(free)==2',"print('FREE',free,flush=True); assert len(free)==2")
exec(source)
