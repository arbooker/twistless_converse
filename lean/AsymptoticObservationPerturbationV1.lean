module

public import AsymptoticNormalPerturbationV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap

variable {G H J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem normal_inverse_norm_le (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) : ‖(normalEquiv R L hR).symm.toContinuousLinearMap‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  change ‖(normalEquiv R L hR).symm g‖≤1*‖g‖
  rw [one_mul]
  exact inverse_norm_le R L hR g

/-- Perturbation of the actual inverse on the terminal Hilbert space. -/
theorem normal_inverse_sub_norm_le (R S : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (hS : ∀ g,‖g‖≤‖S g‖) :
    ‖(normalEquiv R L hR).symm.toContinuousLinearMap-
      (normalEquiv S L hS).symm.toContinuousLinearMap‖≤
        (‖R‖+‖S‖)*(1+‖L‖^2)*‖R-S‖ := by
  have hi : (normalEquiv R L hR).symm.toContinuousLinearMap.comp (normal R L)=1 := by
    apply ContinuousLinearMap.ext
    intro g
    exact (normalEquiv R L hR).symm_apply_apply g
  have hj : (normal S L).comp (normalEquiv S L hS).symm.toContinuousLinearMap=1 := by
    apply ContinuousLinearMap.ext
    intro g
    exact (normalEquiv S L hS).apply_symm_apply g
  exact (inverse_sub_norm_le _ _ _ _ hi hj
    (normal_inverse_norm_le R L hR) (normal_inverse_norm_le S L hS)).trans
      (normal_sub_norm_le R S L)

omit [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] in
theorem sandwich_sub_norm_le_general (R S : G →L[ℂ] H) (I J : G →L[ℂ] G) :
    ‖R.comp (I.comp R.adjoint)-S.comp (J.comp S.adjoint)‖≤
      (‖R‖*‖I‖+‖S‖*‖J‖)*‖R-S‖+‖S‖*‖R‖*‖I-J‖ := by
  have he : R.comp (I.comp R.adjoint)-S.comp (J.comp S.adjoint)=
      (R-S).comp (I.comp R.adjoint)+S.comp ((I-J).comp R.adjoint)+
        S.comp (J.comp (R.adjoint-S.adjoint)) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [sub_apply,add_apply,comp_apply,map_sub]
    abel
  have h₁ : ‖(R-S).comp (I.comp R.adjoint)‖≤‖R-S‖*(‖I‖*‖R‖) := by
    apply (opNorm_comp_le _ _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [adjoint.norm_map] using opNorm_comp_le I R.adjoint
  have h₂ : ‖S.comp ((I-J).comp R.adjoint)‖≤‖S‖*(‖I-J‖*‖R‖) := by
    apply (opNorm_comp_le _ _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [adjoint.norm_map] using opNorm_comp_le (I-J) R.adjoint
  have h₃ : ‖S.comp (J.comp (R.adjoint-S.adjoint))‖≤‖S‖*(‖J‖*‖R-S‖) := by
    apply (opNorm_comp_le _ _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [← map_sub,adjoint.norm_map] using opNorm_comp_le J (R.adjoint-S.adjoint)
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add h₁ h₂) h₃).trans_eq (by ring))

omit [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] in
theorem sandwich_sub_norm_le (R S : G →L[ℂ] H) (I J : G →L[ℂ] G)
    (hi : ‖I‖≤1) (hj : ‖J‖≤1) :
    ‖R.comp (I.comp R.adjoint)-S.comp (J.comp S.adjoint)‖≤
      (‖R‖+‖S‖)*‖R-S‖+‖S‖*‖R‖*‖I-J‖ := by
  apply (sandwich_sub_norm_le_general R S I J).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [mul_one] using add_le_add
    (mul_le_mul_of_nonneg_left hi (norm_nonneg R))
    (mul_le_mul_of_nonneg_left hj (norm_nonneg S))

/-- Norm continuity of the positive observation operator, with an explicit
constant. Only reconstruction changes; the observation stack is fixed. -/
theorem operator_sub_norm_le (R S : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (hS : ∀ g,‖g‖≤‖S g‖) :
    ‖operator R L hR-operator S L hS‖≤
      (‖R‖+‖S‖)*(1+‖S‖*‖R‖*(1+‖L‖^2))*‖R-S‖ := by
  apply (sandwich_sub_norm_le R S _ _
    (normal_inverse_norm_le R L hR) (normal_inverse_norm_le S L hS)).trans
  apply (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (normal_inverse_sub_norm_le R S L hR hS) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))).trans_eq
  ring

#print axioms normal_inverse_norm_le
#print axioms normal_inverse_sub_norm_le
#print axioms sandwich_sub_norm_le_general
#print axioms sandwich_sub_norm_le
#print axioms operator_sub_norm_le

end AsymptoticObservation
