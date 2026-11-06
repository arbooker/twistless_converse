module

public import AsymptoticNormalPerturbationV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Perturb the finite-source product I R*R used in the real trace
transfer. The bound separates the reconstruction and inverse errors. -/
theorem gram_product_sub_norm_le_of_bound (R S I J : H →L[ℂ] H) (BR BI δR δI : ℝ)
    (hR : ‖R‖≤BR) (hS : ‖S‖≤BR) (hJ : ‖J‖≤BI)
    (hdR : ‖R-S‖≤δR) (hdI : ‖I-J‖≤δI) :
    ‖I.comp (R.adjoint.comp R)-J.comp (S.adjoint.comp S)‖≤δI*BR^2+BI*(2*BR*δR) := by
  have hBR : 0≤BR := (norm_nonneg R).trans hR
  have hBI : 0≤BI := (norm_nonneg J).trans hJ
  have hδI : 0≤δI := (norm_nonneg (I-J)).trans hdI
  have hg : ‖R.adjoint.comp R‖≤BR^2 := by
    rw [norm_adjoint_comp_self]
    simpa only [pow_two] using pow_le_pow_left₀ (norm_nonneg R) hR 2
  have hgs : ‖R.adjoint.comp R-S.adjoint.comp S‖≤2*BR*δR := by
    apply (gram_sub_norm_le R S).trans
    have hs : ‖R‖+‖S‖≤2*BR := by linarith
    exact mul_le_mul hs hdR (norm_nonneg (R-S)) (by positivity)
  have he : I.comp (R.adjoint.comp R)-J.comp (S.adjoint.comp S)=
      (I-J).comp (R.adjoint.comp R)+J.comp (R.adjoint.comp R-S.adjoint.comp S) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [sub_apply,add_apply,comp_apply,map_sub]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (opNorm_comp_le _ _).trans (mul_le_mul hdI hg (norm_nonneg _) hδI)
  · apply (opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_right hJ (norm_nonneg _)).trans
    exact mul_le_mul_of_nonneg_left hgs hBI

theorem gram_product_sub_norm_le (R S I J : H →L[ℂ] H) (BR δR δI : ℝ)
    (hR : ‖R‖≤BR) (hS : ‖S‖≤BR) (hJ : ‖J‖≤1)
    (hdR : ‖R-S‖≤δR) (hdI : ‖I-J‖≤δI) :
    ‖I.comp (R.adjoint.comp R)-J.comp (S.adjoint.comp S)‖≤δI*BR^2+2*BR*δR := by
  simpa only [one_mul] using gram_product_sub_norm_le_of_bound R S I J BR 1 δR δI hR hS hJ hdR hdI

#print axioms gram_product_sub_norm_le_of_bound
#print axioms gram_product_sub_norm_le

end AsymptoticObservation
