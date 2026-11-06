module

public import QuantitativeSpectralPacketFactorizationV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralPacketDiagonal

open QuantitativeSpectralDeflationChain QuantitativeSpectralPacketAssembly
open QuantitativeSpectralPacketFactor QuantitativeSpectralPacketFactorization
open QuantitativeSpectralTriangularAssembly

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : ClosedSubmodule ℂ H) (B : ℕ → H →L[ℂ] H) (n : ℕ) (c d : ℝ)

theorem diagonalFactor_eq : diagonalFactor U B n c d =
    c • projection U B c 0 + (d-c) • projection U B c n := by
  unfold diagonalFactor diagonal
  rw [Fin.sum_univ_castSucc]
  simp only [weights, blocks, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [← Finset.smul_sum, Fin.sum_univ_eq_sum_range, sum_removed, smul_sub, sub_smul]
  abel

theorem diagonalFactor_selfAdjoint : IsSelfAdjoint (diagonalFactor U B n c d) := by
  change star (∑ i, weights c n d i • blocks U B c n i) = _
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_smul, star_trivial, (blocks_projection U B c n i).isSelfAdjoint.star_eq]

theorem diagonalFactor_gram : star (diagonalFactor U B n c d) * diagonalFactor U B n c d =
    c^2 • projection U B c 0 + (d^2-c^2) • projection U B c n := by
  rw [(diagonalFactor_selfAdjoint U B n c d).star_eq]
  change diagonal (blocks U B c n) (weights c n d) * diagonal (blocks U B c n) (weights c n d) = _
  rw [diagonal_product (blocks U B c n)
    (fun i => (blocks_projection U B c n i).isIdempotentElem.eq)
    (blocks_orthogonal U B c n)]
  unfold diagonal
  rw [Fin.sum_univ_castSucc]
  simp only [weights, blocks, Fin.lastCases_castSucc, Fin.lastCases_last, ← pow_two]
  rw [← Finset.smul_sum, Fin.sum_univ_eq_sum_range, sum_removed, smul_sub, sub_smul]
  abel

/-- The constructed diagonal has exactly the two scalar blocks required
by the previously verified collective logarithmic spectral-mass theorem. -/
theorem diagonalFactor_gram_of_initial_one (hU : projection U B c 0 = 1) :
    star (diagonalFactor U B n c d) * diagonalFactor U B n c d =
      c^2 • (1 : H →L[ℂ] H) + (d^2-c^2) • projection U B c n := by
  rw [diagonalFactor_gram, hU]

#print axioms diagonalFactor_eq
#print axioms diagonalFactor_selfAdjoint
#print axioms diagonalFactor_gram
#print axioms diagonalFactor_gram_of_initial_one

end QuantitativeSpectralPacketDiagonal
