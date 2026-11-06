module

public import AsymptoticPolynomialPerturbationV1
public import AsymptoticGramProductPerturbationV1
public import AsymptoticObservationPerturbationV1
public import AsymptoticRegularObservationNormalBoundV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap AsymptoticCoerciveNeumann

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

noncomputable def polynomialReconstructionLipschitz (C BR BL : ℝ) (n : ℕ) : ℝ :=
  let D := BR^2+(BL*BR)^2+2
  polynomialLipschitz C D n*(2*BR*(1+BL^2))*BR^2+
    polynomialBound C D n*(2*BR)

theorem polynomialReconstructionLipschitz_nonneg (C BR BL : ℝ) (hBR : 0≤BR) (n : ℕ) :
    0≤polynomialReconstructionLipschitz C BR BL n := by
  have hc := (scale_pos C).le
  unfold polynomialReconstructionLipschitz polynomialLipschitz polynomialBound
  positivity

theorem completedNormal_difference_bound (P R S : H →L[ℂ] H) (L : H →L[ℂ] J)
    (BR BL : ℝ) (hR : ‖R‖≤BR) (hS : ‖S‖≤BR) (hL : ‖L‖≤BL) :
    ‖completedNormal P R L-completedNormal P S L‖≤2*BR*(1+BL^2)*‖R-S‖ := by
  have hR0 : 0≤BR := (norm_nonneg R).trans hR
  apply (completedNormal_sub_norm_le P R S L).trans
  have hsum : ‖R‖+‖S‖≤2*BR := by linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hsum (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg L) hL 2))
      (by positivity) (by positivity)) (norm_nonneg _)

/-- The finite-corner trace expression remains uniformly stable after
substituting a finite reconstruction into the completed normal polynomial. -/
theorem polynomial_gram_difference_norm_le (C : ℝ) (P R S : H →L[ℂ] H) (L : H →L[ℂ] J)
    (BR BL : ℝ) (hP : ‖P‖≤1) (hR : ‖R‖≤BR) (hS : ‖S‖≤BR) (hL : ‖L‖≤BL) (n : ℕ) :
    ‖(polynomial C (completedNormal P R L) n).comp (R.adjoint.comp R)-
      (polynomial C (completedNormal P S L) n).comp (S.adjoint.comp S)‖≤
      polynomialReconstructionLipschitz C BR BL n*‖R-S‖ := by
  let D := BR^2+(BL*BR)^2+2
  have hMR : ‖completedNormal P R L‖≤D := completedNormal_norm_le P R L BR BL hP hR hL
  have hMS : ‖completedNormal P S L‖≤D := completedNormal_norm_le P S L BR BL hP hS hL
  have hLip : 0≤polynomialLipschitz C D n := by
    have hc := (scale_pos C).le
    dsimp [polynomialLipschitz,D]
    positivity
  have hi : ‖polynomial C (completedNormal P R L) n-polynomial C (completedNormal P S L) n‖≤
      polynomialLipschitz C D n*(2*BR*(1+BL^2)*‖R-S‖) :=
    (polynomial_difference_norm_le C _ _ hMR hMS n).trans
      (mul_le_mul_of_nonneg_left (completedNormal_difference_bound P R S L BR BL hR hS hL) hLip)
  apply (gram_product_sub_norm_le_of_bound R S _ _ BR (polynomialBound C D n) ‖R-S‖
    (polynomialLipschitz C D n*(2*BR*(1+BL^2)*‖R-S‖)) hR hS
    (polynomial_norm_le_of_bound C _ hMS n) le_rfl hi).trans_eq
  unfold polynomialReconstructionLipschitz
  dsimp [D]
  ring

#print axioms polynomialReconstructionLipschitz_nonneg
#print axioms completedNormal_difference_bound
#print axioms polynomial_gram_difference_norm_le

end AsymptoticObservation
