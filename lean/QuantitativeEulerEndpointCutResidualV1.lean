module

public import QuantitativeEulerEndpointGramResidualV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointResidual
open scoped Classical
variable {A : Type*} [CStarAlgebra A]

/-- Cutting an exact solution introduces precisely its removed-part residual. -/
theorem cut_row_residual (P E R : A) (hRE : R*E=0) :
    ‖R*(P*E)‖≤‖R‖*‖P*E-E‖ := by
  have he : R*(P*E)=R*(P*E-E) := by rw [mul_sub,hRE,sub_zero]
  rw [he]
  exact norm_mul_le _ _

/-- The actual cutoff Gram error is at most the squared row budget times
one common cutoff error; rows are assumed exact only BEFORE cutting. -/
theorem cut_gram_residual {ι : Type*} [Fintype ι] (P E : A) (R : ι → A)
    (hP : ‖P‖≤1) (hPP : P*P=P) (hRE : ∀ i,R i*E=0) :
    ‖(∑ i,star (R i*P)*(R i*P))*(P*E)‖≤
      (∑ i,‖R i‖^2)*‖P*E-E‖ := by
  have hPE : P*(P*E)=P*E := by rw [←mul_assoc,hPP]
  apply (gram_residual P (P*E) R hP hPE).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ‖R i‖*(‖R i‖*‖P*E-E‖) :=
      mul_le_mul_of_nonneg_left (cut_row_residual P E (R i) (hRE i)) (norm_nonneg _)
    _ = _ := by ring

theorem cut_weighted_gram_residual {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P E : A) (R : ι → κ → A) (w : ι → ℝ) (c : ℝ)
    (hP : ‖P‖≤1) (hPP : P*P=P) (hRE : ∀ i j,R i j*E=0) :
    ‖(c • ∑ i,w i • ∑ j,star (R i j*P)*(R i j*P))*(P*E)‖≤
      (|c| * ∑ i,|w i| * ∑ j,‖R i j‖^2)*‖P*E-E‖ := by
  rw [smul_mul_assoc,norm_smul,Real.norm_eq_abs,Finset.sum_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [smul_mul_assoc,norm_smul,Real.norm_eq_abs,mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (cut_gram_residual P E (R i) hP hPP (hRE i)) (abs_nonneg _)

#print axioms cut_row_residual
#print axioms cut_gram_residual
#print axioms cut_weighted_gram_residual
end QuantitativeEulerEndpointResidual
