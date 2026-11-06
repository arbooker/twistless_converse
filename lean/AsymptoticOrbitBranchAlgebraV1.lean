module

public import AsymptoticOrbitBranchV1
public import AsymptoticRegularSignedTraceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open ContinuousLinearMap
open scoped lp

variable {G : Type*}

theorem eq_of_matrix_eq (B C : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (h : ∀ g j,matrix B g j=matrix C g j) : B=C := by
  apply sub_eq_zero.mp
  apply eq_zero_of_columns
  intro j
  apply lp.ext
  funext g
  change B (delta j) g-C (delta j) g=0
  exact sub_eq_zero.mpr (h g j)

end AsymptoticRegularTrace

namespace AsymptoticOrbitBranch

attribute [local instance] Classical.propDecidable

open AsymptoticRegularTrace MeasureTheory ContinuousLinearMap
open scoped lp ComplexConjugate

variable {G α : Type*} [Group G] [MulAction G α]

theorem product_coefficient_bound (a : G) (c d : α → ℂ) {C D : ℝ}
    (hC : 0≤C) (hc : ∀ x,‖c x‖≤C) (hd : ∀ x,‖d x‖≤D) (x : α) :
    ‖c x*d (a • x)‖≤C*D := by
  rw [norm_mul]
  exact mul_le_mul (hc x) (hd (a • x)) (norm_nonneg _) hC

/-- Labels multiply in reverse order because branches act by pullback.
This is the same order as composition of the holomorphic slash operators. -/
theorem operator_comp (a b : G) (c d : α → ℂ) {C D : ℝ}
    (hC : 0≤C) (hD : 0≤D) (hc : ∀ x,‖c x‖≤C) (hd : ∀ x,‖d x‖≤D) (x : α) :
    (operator a c hC hc x).comp (operator b d hD hd x)=
      operator (b*a) (fun x => c x*d (a • x)) (mul_nonneg hC hD)
        (product_coefficient_bound a c d hC hc hd) x := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext g
  simp only [comp_apply,operator_apply,mul_smul,mul_assoc]

theorem adjoint_coefficient_bound (a : G) (c : α → ℂ) {C : ℝ}
    (hc : ∀ x,‖c x‖≤C) (x : α) : ‖conj (c (a⁻¹ • x))‖≤C := by
  simpa only [RCLike.norm_conj] using hc (a⁻¹ • x)

theorem operator_adjoint (a : G) (c : α → ℂ) {C : ℝ}
    (hC : 0≤C) (hc : ∀ x,‖c x‖≤C) (x : α) :
    (operator a c hC hc x).adjoint=
      operator a⁻¹ (fun x => conj (c (a⁻¹ • x))) hC (adjoint_coefficient_bound a c hc) x := by
  classical
  apply eq_of_matrix_eq
  intro g h
  rw [matrix_adjoint,operator_matrix,operator_matrix]
  by_cases he : a*h=g
  · have he' : a⁻¹*g=h := by rw [← he,inv_mul_cancel_left]
    rw [ite_eq_left he,ite_eq_left he',← mul_smul,he']
  · have he' : a⁻¹*g≠h := by
      intro hh
      apply he
      rw [← hh,mul_inv_cancel_left]
    simp only [ite_eq_right he,ite_eq_right he',map_zero]

/-- The regular rooted diagonal selects precisely words whose complete
projective group label is the identity. -/
theorem operator_root (a : G) (c : α → ℂ) {C : ℝ}
    (hC : 0≤C) (hc : ∀ x,‖c x‖≤C) (x : α) :
    matrix (operator a c hC hc x) 1 1=if a=1 then c x else 0 := by
  classical
  simp only [operator_matrix,mul_one,one_smul]

theorem operator_signedTrace [MeasurableSpace α] (μ : Measure α)
    (a : G) (c : α → ℂ) {C : ℝ} (hC : 0≤C) (hc : ∀ x,‖c x‖≤C) :
    signedTrace μ (operator a c hC hc)=if a=1 then ∫ x,(c x).re ∂μ else 0 := by
  classical
  unfold signedTrace
  simp only [operator_root]
  by_cases ha : a=1 <;> simp only [ha,ite_true,ite_false,Complex.zero_re,integral_zero]

#print axioms AsymptoticRegularTrace.eq_of_matrix_eq
#print axioms operator_comp
#print axioms operator_adjoint
#print axioms operator_root
#print axioms operator_signedTrace

end AsymptoticOrbitBranch
