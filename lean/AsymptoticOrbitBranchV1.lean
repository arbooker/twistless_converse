module

public import AsymptoticOrbitDiagonalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticOrbitBranch

open AsymptoticRegularTrace MeasureTheory ContinuousLinearMap
open scoped lp

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

noncomputable def reindexLinear (e : ι ≃ ι) : ℓ²(ι,ℂ) →ₗ[ℂ] ℓ²(ι,ℂ) where
  toFun f := ⟨fun i => f (e i),memℓp_gen ((e.summable_iff).mpr
    ((lp.memℓp f).summable (by norm_num)))⟩
  map_add' f g := by apply lp.ext; rfl
  map_smul' c f := by apply lp.ext; rfl

theorem reindex_norm (e : ι ≃ ι) (f : ℓ²(ι,ℂ)) : ‖reindexLinear e f‖=‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h₁ : HasSum (fun i => ‖reindexLinear e f i‖^2) (‖reindexLinear e f‖^2) := by
    simpa using lp.hasSum_norm (p:=2) (by norm_num) (reindexLinear e f)
  have h₂ : HasSum (fun i => ‖f i‖^2) (‖f‖^2) := by
    simpa using lp.hasSum_norm (p:=2) (by norm_num) f
  exact h₁.unique (e.hasSum_iff.mpr h₂)

noncomputable def reindex (e : ι ≃ ι) : ℓ²(ι,ℂ) →ₗᵢ[ℂ] ℓ²(ι,ℂ) :=
  ⟨reindexLinear e,reindex_norm e⟩

variable {G α : Type*} [Group G] [MulAction G α]

/-- A weighted branch on actual counting coordinates of an orbit. The
root x parametrizes the family; no holomorphic values enter ℓ². -/
noncomputable def operator (a : G) (c : α → ℂ) {C : ℝ}
    (hC : 0≤C) (hc : ∀ x,‖c x‖≤C) (x : α) : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) :=
  (AsymptoticOrbitDiagonal.operator (fun g : G => c (g • x)) hC (fun g => hc (g • x))).comp
    (reindex (Equiv.mulLeft a)).toContinuousLinearMap

theorem operator_apply (a : G) (c : α → ℂ) {C : ℝ}
    (hC : 0≤C) (hc : ∀ x,‖c x‖≤C) (x : α) (f : ℓ²(G,ℂ)) (g : G) :
    operator a c hC hc x f g=c (g • x)*f (a*g) := rfl

theorem operator_norm_le (a : G) (c : α → ℂ) {C : ℝ}
    (hC : 0≤C) (hc : ∀ x,‖c x‖≤C) (x : α) : ‖operator a c hC hc x‖≤C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  exact ((AsymptoticOrbitDiagonal.operator _ hC (fun g : G => hc (g • x))).le_of_opNorm_le
    (AsymptoticOrbitDiagonal.operator_norm_le _ _ _) _).trans_eq
      (congrArg (fun r : ℝ => C*r) ((reindex (Equiv.mulLeft a)).norm_map f))

theorem operator_matrix (a : G) (c : α → ℂ) {C : ℝ}
    (hC : 0≤C) (hc : ∀ x,‖c x‖≤C) (x : α) (g h : G) :
    matrix (operator a c hC hc x) g h=if a*g=h then c (g • x) else 0 := by
  classical
  by_cases he : a*g=h
  · simp [matrix,operator_apply,delta,he]
  · simp [matrix,operator_apply,delta,he]

theorem operator_covariant (a : G) (c : α → ℂ) {C : ℝ}
    (hC : 0≤C) (hc : ∀ x,‖c x‖≤C) : Covariant (operator a c hC hc) := by
  intro x b g h
  simp only [operator_matrix,mul_smul,← mul_assoc,mul_right_cancel_iff]

theorem operator_matrix_measurable [MeasurableSpace α]
    (hact : ∀ g : G,Measurable (fun x : α => g • x))
    (a : G) (c : α → ℂ) {C : ℝ} (hC : 0≤C) (hc : ∀ x,‖c x‖≤C)
    (hcm : Measurable c) (g h : G) :
    Measurable (fun x => matrix (operator a c hC hc x) g h) := by
  classical
  simp only [operator_matrix]
  by_cases he : a*g=h
  · simpa only [ite_eq_left he,Function.comp_def] using hcm.comp (hact g)
  · simp only [ite_eq_right he]
    exact measurable_const

#print axioms reindex_norm
#print axioms operator_norm_le
#print axioms operator_covariant
#print axioms operator_matrix_measurable

end AsymptoticOrbitBranch
