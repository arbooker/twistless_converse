module

public import QuantitativeHolomorphicGramV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open ContinuousLinearMap QuantitativeHolomorphic
namespace QuantitativeMaass

/-- Positive rescaling of a strictly positive Gram has the expected inverse
square root, proved in the actual continuous functional calculus. -/
theorem inverseSqrtCFC_positive_square_smul {𝔄 : Type*} [CStarAlgebra 𝔄]
    (A : 𝔄) (hA : IsSelfAdjoint A) {a c : ℝ} (ha : 0<a) (hc : 0<c)
    (hlo : ∀ x∈spectrum ℝ A,a≤x) :
    inverseSqrtCFC ((c^2) • A)=c⁻¹ • inverseSqrtCFC A := by
  have hf := inverseSqrt_continuousOn ha A hlo
  have hg : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹)
      ((fun x : ℝ => c^2*x) '' spectrum ℝ A) := by
    apply Real.continuous_sqrt.continuousOn.inv₀
    rintro y ⟨x,hx,rfl⟩
    exact (Real.sqrt_pos.mpr (mul_pos (sq_pos_of_pos hc) (ha.trans_le (hlo x hx)))).ne'
  unfold inverseSqrtCFC
  rw [←cfc_comp_const_mul (c^2) (fun x : ℝ => (Real.sqrt x)⁻¹) A hg hA]
  calc
    _ = cfc (fun x : ℝ => c⁻¹*(Real.sqrt x)⁻¹) A := by
      apply cfc_congr
      intro x _hx
      change (Real.sqrt (c^2*x))⁻¹=c⁻¹*(Real.sqrt x)⁻¹
      rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc.le,mul_inv_rev]
      ring
    _ = _ := cfc_const_mul c⁻¹ _ A hf

/-- Positive scalar normalization leaves the exact reconstruction isometry
unchanged. This connects a contractive Newton input to the original map. -/
theorem normalizedReconstruction_positive_smul {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : G→L[ℂ]H) {a c : ℝ} (ha : 0<a) (hc : 0<c)
    (hR : ∀ x,a*‖x‖^2≤‖R x‖^2) :
    normalizedReconstruction (c • R)=normalizedReconstruction R := by
  have hadj : (c • R).adjoint=c • R.adjoint := by
    change ((c:ℂ) • R).adjoint=(c:ℂ) • R.adjoint
    rw [map_smulₛₗ]
    simp
  have hgram : (c • R).adjoint.comp (c • R)=(c^2) • (R.adjoint.comp R) := by
    rw [hadj,smul_comp,comp_smul,smul_smul,pow_two]
  have hA := (isPositive_adjoint_comp_self R).isSelfAdjoint
  have hlo := (algebraMap_le_iff_le_spectrum hA).mp (reconstruction_gram_lower R hR)
  unfold normalizedReconstruction
  rw [hgram,inverseSqrtCFC_positive_square_smul (R.adjoint.comp R) hA ha hc hlo,
    smul_comp,comp_smul,smul_smul,mul_inv_cancel₀ hc.ne',one_smul]

#print axioms inverseSqrtCFC_positive_square_smul
#print axioms normalizedReconstruction_positive_smul
end QuantitativeMaass
