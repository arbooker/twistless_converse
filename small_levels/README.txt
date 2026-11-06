Small-level companion calculations

This directory accompanies ../pdf/small_level_converse.pdf. It contains
251 computational source, data and provenance-helper files, including the level-25 negative-chart
input. Exact file hashes are recorded in ../lean/SOURCE_MANIFEST.json.

The document-provenance helper reads recorded document hashes from
../provenance/SMALL_LEVEL_COMPANIONS_20261105.json. Generated audits identify
these inventory references separately; computational files are hashed from
their current bytes.

The Lean proofs are checked separately using ../BUILD.txt. Rebuilding Lean
does not require running these research generators or a computer algebra
system. The companion inventory and input audit are static checks, not a claim
that every historical computation has been rerun.

Environment and paths

Use a disposable local checkout, preserving the small_levels layout,
and run commands from the repository root. The Python programs use Python 3;
SymPy is the only nonstandard Python import found by the static audit. Files
ending in .m are Magma programs or inputs emitted for Magma. Historical JSON
records may name other tools used in the original calculations. No universal
Python/SymPy/Magma version or resource bound has been verified for this entire
collection; individual programs and records specify their own requirements.

Many programs write fixed names in /tmp, and some write beside their sources.
Run dependent steps sequentially in a disposable environment with a fresh /tmp.
Do not run competing calculations using the same scratch filenames. Some
generators are substantial computations; packaging did not rerun them.

Selected input chains

Level 19: generate the first-jet Magma input before the sparse-membership
preparer reads its header:

  python3 small_levels/level19_firstjet_certificate.py
  python3 small_levels/level19_exact_membership_sparse_prepare.py

The first command writes /tmp/level19_firstjet_certificate.m. The second emits
/tmp/level19_exact_membership_sparse.m and its manifest. These commands emit
inputs; they do not themselves execute Magma or certify a successful Magma run.

Level 25: the recovered seed-0 chart-2 input must be at the fixed path used by
the negative-chart preparer:

  cp small_levels/level25_cusp_aux_minus_seed0_chart2.txt /tmp/
  python3 small_levels/level25_plus_poles_negative2_prepare.py 2 seed0

The input SHA256 is
b2d9fb99e6e0af225a21a4881e1b33fdfb5eddcdc986627d28cd7747feedb7c0.
The default command emits rational full-chart Magma input at
/tmp/level25_plus_poles_negative2_even2_rational_full.m. The optional finite
mode is exploratory and is not a rational certificate. Only seed 0, chart 2
is supplied by this recovered input; other seed arguments need their own data.
level25_root_chart1_modulus.py uses the packaged rational-center certificate;
its historical /tmp fallback is needed only when that certificate is absent.

Level 35: level35_firstjet_projection.py inherits its three sign arguments
from level35_full_continuation.py and always writes the same reduced filename.
For the positive-product residue calculation, run the positive signs and copy
that result before the residue emitter:

  python3 small_levels/level35_firstjet_projection.py 1 -1 -1
  cp /tmp/level35_firstjet_reduced.json /tmp/level35_firstjet_positive.json
  python3 small_levels/level35_positive_residue.py

The residue emitter checks the regenerated rows against the packaged rows and
source hashes, then writes /tmp/level35_positive_residue.m. For the negative
unshifted residue, regenerate with signs -1 -1 -1 before running
level35_unshifted_residue.py. Do not reuse the positive reduced output for it.
level35_positive_gap1.py checks the positive regenerated output if present;
that optional comparison is distinct from the mandatory input to the positive
residue emitter.

These recipes follow the source-level read/write chains; they were not executed
as part of packaging. Other scripts may have their own generated inputs. The
dated static closure and I/O-site inventories in ../provenance/ identify
those sites, including unresolved dynamic paths and historical log references.
An unresolved string alone does not establish a missing runtime dependency.
