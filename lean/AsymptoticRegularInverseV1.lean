module

public import AsymptoticRegularAlgebraV1
public import AsymptoticCoerciveInverseV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap InnerProductSpace AsymptoticCoerciveNeumann
open scoped lp

variable {G α : Type*} [Group G] [MulAction G α]

theorem covariant_sub (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Covariant B) (hC : Covariant C) : Covariant (fun x => B x-C x) := by
  intro x a g h
  change matrixCLM g h (B (a • x)-C (a • x))=matrixCLM (g*a) (h*a) (B x-C x)
  rw [map_sub,map_sub]
  exact congrArg₂ (·-·) (hB x a g h) (hC x a g h)

theorem step_covariant (C : ℝ) (M : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hM : Covariant M) : Covariant (fun x => step C (M x)) :=
  covariant_sub _ _ covariant_one (covariant_smul _ _ hM)

theorem inverse_covariant (C : ℝ) (M : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hM : Covariant M) (hb : ∀ x,‖M x‖≤C)
    (hc : ∀ x f,‖f‖^2≤(⟪M x f,f⟫_ℂ).re) :
    Covariant (fun x => inverse C (M x)) := by
  apply covariant_smul
  apply covariant_tsum
  · intro x
    exact summable_geometric_of_norm_lt_one (step_norm_lt_one C (M x) (hb x) (hc x))
  · intro n
    exact covariant_pow _ (step_covariant C M hM) n

variable [MeasurableSpace α]

omit [Group G] [MulAction G α] in
theorem matrix_sub_measurable (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hC : ∀ g h,Measurable (fun x => matrix (C x) g h)) (g h : G) :
    Measurable (fun x => matrix (B x-C x) g h) := by
  have he (x : α) : matrix (B x-C x) g h=matrix (B x) g h-matrix (C x) g h :=
    map_sub (matrixCLM g h) (B x) (C x)
  simp only [he]
  exact (hB g h).sub (hC g h)

omit [Group G] [MulAction G α] in
theorem step_matrix_measurable (C : ℝ) (M : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hM : ∀ g h,Measurable (fun x => matrix (M x) g h)) (g h : G) :
    Measurable (fun x => matrix (step C (M x)) g h) :=
  matrix_sub_measurable _ _ (fun _ _ => measurable_const) (matrix_smul_measurable _ _ hM) g h

omit [Group G] [MulAction G α] in
theorem inverse_matrix_measurable [Countable G]
    (C : ℝ) (M : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hM : ∀ g h,Measurable (fun x => matrix (M x) g h)) (hb : ∀ x,‖M x‖≤C)
    (hc : ∀ x f,‖f‖^2≤(⟪M x f,f⟫_ℂ).re) (g h : G) :
    Measurable (fun x => matrix (inverse C (M x)) g h) := by
  apply matrix_smul_measurable
  intro a b
  apply matrix_tsum_measurable
  · intro x
    exact summable_geometric_of_norm_lt_one (step_norm_lt_one C (M x) (hb x) (hc x))
  · intro n u v
    exact matrix_pow_measurable _ (step_matrix_measurable C M hM) n u v

#print axioms inverse_covariant
#print axioms inverse_matrix_measurable

end AsymptoticRegularTrace
