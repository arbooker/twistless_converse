module

public import AsymptoticHolomorphicTraceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap

variable {G H J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- Orthogonal compression cannot increase the norm of a perturbation. -/
theorem holomorphicOperator_sub_norm_le (R S : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (hS : ∀ g,‖g‖≤‖S g‖) (U : Submodule ℂ H) [CompleteSpace U] :
    ‖holomorphicOperator R L hR U-holomorphicOperator S L hS U‖≤
      ‖operator R L hR-operator S L hS‖ := by
  have he : holomorphicOperator R L hR U-holomorphicOperator S L hS U=
      U.subtypeL.adjoint.comp ((operator R L hR-operator S L hS).comp U.subtypeL) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [holomorphicOperator,sub_apply,comp_apply,map_sub]
  have hu : ‖U.subtypeL‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    simp
  have hua : ‖U.subtypeL.adjoint‖≤1 := by rwa [adjoint.norm_map]
  rw [he]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right hua (norm_nonneg _)).trans
  rw [one_mul]
  apply (opNorm_comp_le _ _).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hu
    (norm_nonneg (operator R L hR-operator S L hS))

#print axioms holomorphicOperator_sub_norm_le

end AsymptoticObservation
