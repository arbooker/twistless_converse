"""Explore normalized higher Taylor compatibility on the closed N26 Q390 system.
Only Laurent monomial pivots are inverted. This is not a global pole theorem:
falling-factorial normalization requires separate treatment at weight endpoints,
and nonmonomial specialized rank assertions are not uniform.
Use N26_ORDERS, N26_EXPORT; do not set N26_H (old specialization has fewer primes).
"""
from pathlib import Path
import os
assert os.environ.get('N26_H') is None
base=Path(__file__).parent
wide=True
exec((base/('level26_prime5_wide_closed.py' if 'grid780' in __import__('sys').argv else 'level26_prime5_closed.py')).read_text())
text=(base/'level34_finish_first_jet.py').read_text()
text=text[text.index('original = '):text.index('kernels = []; sources = []')]
text=text.replace('[0][0][3:]','[0][0][4:]').replace('17**(n*pw[2]))','13**(n*pw[2]) * 5**(n*pw[3]))')
exec(text)
assert (Q,free,len(piv)) in [(390,[150,270],193),(780,[300,540],318)]
higher=(base/'level26_finish_higher.py').read_text()
higher=higher[higher.index('from math import factorial'):]
exec(higher)
