"""Uniform leading continuation audit for the closed320 Q780 system."""
from pathlib import Path
src=Path(__file__).with_name('level26_prime5_continuation.py').read_text()
src=src.replace('level26_prime5_closed.py','level26_prime5_wide_closed.py')
src=src.replace('len(U)==195 and len(piv)==195','len(U)==320 and len(piv)==320')
src=src.replace('level26_prime5_continuation_','level26_prime5_wide_continuation_')
exec(src)
