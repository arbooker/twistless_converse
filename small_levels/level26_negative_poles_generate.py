"""Regenerate the exact order-two meromorphic-germ equations, one sign case.

The actual certificate uses polynomial left syzygies to eliminate all lower
germs; it never bounds their pole orders by the top-point pole order.
"""
from pathlib import Path
import os
import sys

assert len(sys.argv)>=4
signs=list(map(int,sys.argv[1:4]));assert signs[2]==-1
code=''.join('p' if z==1 else 'm' for z in signs)
if 'grid780' not in sys.argv:sys.argv.append('grid780')
os.environ['N26_ORDERS']='2'
os.environ['N26_EXPORT']='/tmp/level26_negative_poles_higher2_'+code+'.json'
base=Path(__file__).parent
source=(base/'level26_root_prime5_higher.py').read_text()
source=source.replace('assert (Q,free,len(piv)) in [(390,[150,270],193),(780,[300,540],318)]',
                      'assert Q==780 and len(free)==2 and len(piv)==318')
exec(source)
