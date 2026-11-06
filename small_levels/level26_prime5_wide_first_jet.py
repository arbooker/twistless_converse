"""Exact monomial-only first-source reduction on the Q780 closed320 system."""
from pathlib import Path
src=Path(__file__).with_name('level26_prime5_first_jet.py').read_text()
src=src.replace('level26_prime5_closed.py','level26_prime5_wide_closed.py')
src=src.replace('range(0,Q,5)','range(0,Q,Q//78)')
exec(src)
