Towards a twistless converse theorem: supplementary material

All formal proofs and writeups in this repository were written by GPT-6 Astra.

Written proofs (PDF)

pdf/asymptotic_euler_count.pdf
  The asymptotic count under the radical condition.
pdf/small_level_converse.pdf
  Small-level converse theorems and the common exact-count argument.
pdf/maass_finiteness.pdf
  Fixed-parameter finiteness and shrinking spectral windows at admissible levels.
pdf/rank_verification_toolkit.pdf
  Structural reductions and exact rank certificates for Ramanujan row matrices.
pdf/small_conductor_twists.pdf
  The prime-level converse theorem with twists below the square root of the level.

Formal proofs

lean/ contains Lean sources for Theorems 1.1--1.3 and the prime-level
small-conductor converse, including the primitive multiplicative-twist
corollary. ReleaseCheck.lean lists the endpoints. Exact source hashes and
dependency pins are in lean/SOURCE_MANIFEST.json; dated verification records
identify the sources and declarations they check. See BUILD.txt for the
kernel-checking commands.

Computations

numerics/ contains the numerical programs and their build instructions.
small_levels/ contains computational companions and recorded inputs;
its README.txt explains prerequisites and generator ordering.

See BUILD.txt for verification instructions and LICENSE for licensing.
