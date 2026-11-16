Towards a twistless converse theorem: supplementary material

All formal proofs and writeups in this repository were written by GPT-6 Astra.

Companion to A. R. Booker, M. Lee and N. Zubrilina, Towards a twistless
converse theorem, https://arxiv.org/abs/2611.07921.

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

lean/ contains the formal proofs of Theorems 1.1--1.3, the prime-level
small-conductor converse and its primitive-twist corollary, the spanning
criterion, and the short-interval Weyl asymptotic for the original Maass
Euler-product solution count at all admissible levels.

The six theorem roots and their 17 audited conclusions are listed in
lean/SOURCE_MANIFEST.json. The release contains 5,681 kernel-checked modules;
verification records give their exact source hashes, dependency fingerprints
and axiom reports. See BUILD.txt for reproduction commands.

Computations

numerics/ contains the numerical programs and their build instructions.
small_levels/ contains computational companions and recorded inputs;
its README.txt explains prerequisites and generator ordering.

See BUILD.txt for verification instructions and LICENSE for licensing.
