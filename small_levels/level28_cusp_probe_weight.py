"""Exact leading-ideal membership used to exclude s=k for N28, k>=4.
The elementary all-weight inequality is proved in the accompanying TeX.
"""
from pathlib import Path
import contextlib,io
base=Path(__file__).parent
with contextlib.redirect_stdout(io.StringIO()):
    exec((base/'level28_root_weight_probe.py').read_text())
target=(Y**2-1)*((Z+eta)**2-(4*Y**2 if eta*bad7==1 else 12*Y**2+4))
assert g.reduce(sp.expand(target))[1]==0
if eta==bad7==-1:
    assert g.reduce(sp.expand((Y**2-1)*(A*Y+Y**2+1)))[1]==0
print('EXACT_WEIGHT_ELIMINANT_VERIFIED',eta,bad7,sp.factor(target),flush=True)
for m in range(1,101):
    value=target.subs({Y:3**m,Z:7**m})
    assert (value==0)==(m==1 and eta==bad7==-1)
print('FINITE_WEIGHT_SANITY_CHECK_1_TO_100_PASS; uniform proof in TeX',flush=True)
