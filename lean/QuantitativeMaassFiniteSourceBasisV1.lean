module

public import QuantitativeMaassFiniteSourceEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeMaass

variable {E H ι κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

/-- Finite source energy is independent of the chosen orthonormal basis,
even when the output lies in an infinite-dimensional Hilbert space. -/
theorem finiteSourceEnergy_basis_independent (b : OrthonormalBasis ι ℂ E)
    (c : OrthonormalBasis κ ℂ E) (A : E→L[ℂ]H) :
    finiteSourceEnergy b A=finiteSourceEnergy c A := by
  have hn : ‖ContinuousLinearMap.id ℂ E‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp only [ContinuousLinearMap.id_apply,one_mul,le_refl]
  have hn2 := pow_le_pow_left₀ (norm_nonneg (ContinuousLinearMap.id ℂ E)) hn 2
  simp only [one_pow] at hn2
  have hbc := finiteSourceEnergy_right b c A (ContinuousLinearMap.id ℂ E)
  have hcb := finiteSourceEnergy_right c b A (ContinuousLinearMap.id ℂ E)
  simp only [ContinuousLinearMap.comp_id] at hbc hcb
  apply le_antisymm
  · exact hbc.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn2 (finiteSourceEnergy_nonneg c A))
  · exact hcb.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn2 (finiteSourceEnergy_nonneg b A))

#print axioms finiteSourceEnergy_basis_independent
end QuantitativeMaass
