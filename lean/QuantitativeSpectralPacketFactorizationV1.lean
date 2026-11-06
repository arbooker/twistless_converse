module

public import QuantitativeSpectralPacketFactorV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralPacketFactorization

open QuantitativeSpectralDeflationChain QuantitativeSpectralPacketAssembly
open QuantitativeSpectralPacketFactor QuantitativeSpectralTriangularAssembly

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : ClosedSubmodule ℂ H) (B : ℕ → H →L[ℂ] H) {c : ℝ} (hc : 0 < c)
  (n : ℕ) {d : ℝ} (hd : 0 < d)

/-- The diagonal factor and strict triangular operator are explicit functions
of the original residual packet, its threshold, and its final regularization. -/
def diagonalFactor (c d : ℝ) : H →L[ℂ] H := diagonal (blocks U B c n) (weights c n d)

def strictFactor (c d : ℝ) : H →L[ℂ] H :=
  normalizedStrict (blocks U B c n) (rows U B c n d) (weights c n d)

include hc hd in
private theorem weights_ne_zero (i : Fin (n+1)) : weights c n d i ≠ 0 := by
  refine Fin.lastCases ?_ (fun _ => ?_) i
  · simpa only [weights, Fin.lastCases_last] using hd.ne'
  · simpa only [weights, Fin.lastCases_castSucc] using hc.ne'

include hc hd in
/-- Strict block triangularity is a theorem about the actual deflation
packet, not a hypothesis on a chosen factor. -/
theorem strictFactor_below :
    QuantitativeSpectralBlockTriangular.Below (blocks U B c n) (strictFactor U B n c d) 1 :=
  normalizedStrict_below (blocks U B c n)
    (fun i => (blocks_projection U B c n i).isIdempotentElem.eq)
    (blocks_orthogonal U B c n) (rows U B c n d)
    (rows_left_supported U B n hc d) (weights c n d)
    (weights_ne_zero hc n hd) (rows_diagonal U B n hc d) (rows_upper U B c n d)

include hc hd in
/-- On the represented source Hilbert space the initial projection is the
identity; the finite packet then has an actual invertible diagonal factor. -/
theorem diagonalFactor_isUnit (hU : projection U B c 0 = 1) :
    IsUnit (diagonalFactor U B n c d) :=
  diagonal_isUnit (blocks U B c n)
    (fun i => (blocks_projection U B c n i).isIdempotentElem.eq)
    (blocks_orthogonal U B c n) ((sum_blocks U B c n).trans hU)
    (weights c n d) (weights_ne_zero hc n hd)

include hc hd in
theorem factorization (hU : projection U B c 0 = 1) :
    diagonalFactor U B n c d * (1 + strictFactor U B n c d) = ∑ i, rows U B c n d i :=
  diagonal_factor (blocks U B c n)
    (fun i => (blocks_projection U B c n i).isIdempotentElem.eq)
    (blocks_orthogonal U B c n) (rows U B c n d) ((sum_blocks U B c n).trans hU)
    (weights c n d) (weights_ne_zero hc n hd)

include hc in
/-- The final retained row adds exactly `d² P`, with no multiplicative loss
on the residual Gram sum. -/
theorem rows_gram_le :
    star (∑ i, rows U B c n d i) * (∑ i, rows U B c n d i) ≤
      (∑ i : Fin n, star (B i) * B i) + d^2 • projection U B c n := by
  rw [row_sum_gram (blocks U B c n) (blocks_orthogonal U B c n)
    (rows U B c n d) (rows_left_supported U B n hc d)
    (fun i => (blocks_projection U B c n i).isSelfAdjoint)]
  rw [Fin.sum_univ_castSucc]
  simp only [rows, Fin.lastCases_castSucc, Fin.lastCases_last]
  have hs : star (projection U B c n) = projection U B c n :=
    by simpa only [blocks, Fin.lastCases_last] using
      (blocks_projection U B c n (Fin.last n)).isSelfAdjoint.star_eq
  have hi : projection U B c n * projection U B c n = projection U B c n :=
    by simpa only [blocks, Fin.lastCases_last] using
      (blocks_projection U B c n (Fin.last n)).isIdempotentElem.eq
  rw [star_smul, star_trivial, hs, smul_mul_assoc, mul_smul_comm, hi, smul_smul, ← pow_two]
  exact add_le_add (Finset.sum_le_sum (fun (i : Fin n) _ => packetRow_gram_le U B hc i)) le_rfl

include hc hd in
theorem factor_gram_le (hU : projection U B c 0 = 1) :
    star (diagonalFactor U B n c d * (1 + strictFactor U B n c d)) *
      (diagonalFactor U B n c d * (1 + strictFactor U B n c d)) ≤
      (∑ i : Fin n, star (B i) * B i) + d^2 • projection U B c n := by
  rw [factorization U B hc n hd hU]
  exact rows_gram_le U B hc n

#print axioms strictFactor_below
#print axioms diagonalFactor_isUnit
#print axioms factorization
#print axioms rows_gram_le
#print axioms factor_gram_le

end QuantitativeSpectralPacketFactorization
