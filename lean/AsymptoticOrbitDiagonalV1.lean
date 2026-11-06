module

public import AsymptoticRegularNormalV1
public import Mathlib.Analysis.Normed.Lp.lpHolder

set_option autoImplicit false
@[expose] public section

namespace AsymptoticOrbitDiagonal

open AsymptoticRegularTrace MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped lp ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

/-- Bounded multiplication on a counting Hilbert space. -/
noncomputable def operator (c : ι → ℂ) {C : ℝ} (hC : 0≤C) (hc : ∀ i, ‖c i‖≤C) :
    ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ) :=
  lp.mapCLM 2 (fun i => c i • ContinuousLinearMap.id ℂ ℂ) hC
    (fun i => by simpa only [norm_smul,norm_id,mul_one] using hc i)

theorem operator_apply (c : ι → ℂ) {C : ℝ} (hC : 0≤C) (hc : ∀ i, ‖c i‖≤C)
    (f : ℓ²(ι,ℂ)) (i : ι) : operator c hC hc f i=c i*f i := rfl

theorem operator_norm_le (c : ι → ℂ) {C : ℝ} (hC : 0≤C) (hc : ∀ i, ‖c i‖≤C) :
    ‖operator c hC hc‖≤C := lp.norm_mapCLM_le _ _ _ _

theorem operator_delta (c : ι → ℂ) {C : ℝ} (hC : 0≤C) (hc : ∀ i, ‖c i‖≤C)
    (i : ι) : operator c hC hc (delta i)=c i • delta i := by
  classical
  apply lp.ext
  funext j
  by_cases hj : j=i
  · subst j
    simp [operator_apply,delta]
  · simp [operator_apply,delta,lp.coeFn_smul,hj]

theorem operator_matrix (c : ι → ℂ) {C : ℝ} (hC : 0≤C) (hc : ∀ i, ‖c i‖≤C)
    (i j : ι) : matrix (operator c hC hc) i j=if i=j then c i else 0 := by
  classical
  by_cases hij : i=j
  · subst j
    simp [matrix,operator_apply,delta]
  · simp [matrix,operator_apply,delta,hij]

theorem operator_adjoint (c : ι → ℂ) {C : ℝ} (hC : 0≤C) (hc : ∀ i, ‖c i‖≤C) :
    (operator c hC hc).adjoint=
      operator (fun i => conj (c i)) hC (fun i => by simpa using hc i) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [operator_apply,RCLike.inner_apply,map_mul,starRingEnd_apply,star_star]
  ring

theorem unit_norm (c : ι → ℂ) (hc : ∀ i, ‖c i‖=1) (f : ℓ²(ι,ℂ)) :
    ‖operator c zero_le_one (fun i => (hc i).le) f‖=‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h₁ : HasSum (fun i => ‖operator c zero_le_one (fun i => (hc i).le) f i‖^2)
      (‖operator c zero_le_one (fun i => (hc i).le) f‖^2) := by
    simpa using lp.hasSum_norm (p:=2) (by norm_num)
      (operator c zero_le_one (fun i => (hc i).le) f)
  have h₂ : HasSum (fun i => ‖f i‖^2) (‖f‖^2) := by
    simpa using lp.hasSum_norm (p:=2) (by norm_num) f
  simp only [operator_apply,norm_mul,hc,one_mul] at h₁
  exact h₁.unique h₂

theorem unit_adjoint_mul (c : ι → ℂ) (hc : ∀ i, ‖c i‖=1) :
    (operator c zero_le_one (fun i => (hc i).le)).adjoint.comp
      (operator c zero_le_one (fun i => (hc i).le))=ContinuousLinearMap.id ℂ _ := by
  rw [operator_adjoint]
  apply DFunLike.ext
  intro f
  apply lp.ext
  funext i
  simp only [comp_apply,operator_apply,id_apply]
  rw [← mul_assoc,Complex.conj_mul',hc]
  simp

theorem unit_mul_adjoint (c : ι → ℂ) (hc : ∀ i, ‖c i‖=1) :
    (operator c zero_le_one (fun i => (hc i).le)).comp
      (operator c zero_le_one (fun i => (hc i).le)).adjoint=ContinuousLinearMap.id ℂ _ := by
  rw [operator_adjoint]
  apply DFunLike.ext
  intro f
  apply lp.ext
  funext i
  simp only [comp_apply,operator_apply,id_apply]
  rw [← mul_assoc,Complex.mul_conj',hc]
  simp

section Orbit

variable {G α : Type*} [Group G] [MulAction G α]

/-- A measurable region acts by its indicator on every point of the
orbit. In particular this constructs the strip and terminal corners. -/
noncomputable def corner (s : Set α) (x : α) : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) := by
  classical
  exact operator (fun g : G => if g • x∈s then 1 else 0) zero_le_one
    (fun g => by split_ifs <;> norm_num)

theorem corner_apply (s : Set α) (x : α) (f : ℓ²(G,ℂ)) (g : G) :
    corner s x f g=if g • x∈s then f g else 0 := by
  classical
  simp only [corner,operator_apply]
  split_ifs <;> simp

theorem corner_delta (s : Set α) (x : α) (g : G) :
    corner s x (delta g)=if g • x∈s then delta g else 0 := by
  rw [corner,operator_delta]
  split_ifs <;> simp

theorem corner_matrix (s : Set α) (x : α) (g h : G) :
    matrix (corner s x) g h=if g=h ∧ g • x∈s then 1 else 0 := by
  classical
  rw [corner,operator_matrix]
  by_cases hgh : g=h
  · subst h
    simp
  · simp [hgh]

theorem corner_covariant (s : Set α) : Covariant (corner (G:=G) s) := by
  intro x a g h
  simp only [corner_matrix,mul_right_cancel_iff,mul_smul]

theorem corner_idempotent (s : Set α) (x : α) :
    (corner (G:=G) s x).comp (corner s x)=corner s x := by
  apply DFunLike.ext
  intro f
  apply lp.ext
  funext g
  simp only [comp_apply,corner_apply]
  split_ifs <;> rfl

theorem corner_adjoint (s : Set α) (x : α) :
    (corner (G:=G) s x).adjoint=corner s x := by
  rw [corner,operator_adjoint]
  apply DFunLike.ext
  intro f
  apply lp.ext
  funext g
  simp only [operator_apply]
  split_ifs <;> simp

theorem corner_positive (s : Set α) (x : α) : (corner (G:=G) s x).IsPositive := by
  have h := ContinuousLinearMap.isPositive_adjoint_comp_self (corner (G:=G) s x)
  rwa [corner_adjoint,corner_idempotent] at h

variable [MeasurableSpace α]

theorem corner_matrix_measurable (hact : ∀ g : G, Measurable (fun x : α => g • x))
    {s : Set α} (hs : MeasurableSet s) (g h : G) :
    Measurable (fun x => matrix (corner s x) g h) := by
  classical
  simp only [corner_matrix]
  by_cases hgh : g=h
  · simp only [hgh,true_and]
    exact measurable_const.piecewise (hs.preimage (hact h)) measurable_const
  · simp only [hgh,false_and,ite_false]
    exact measurable_const

omit [MulAction G α] in
theorem root_delta_norm : ‖delta (1 : G)‖=1 := by
  classical
  simp [delta,lp.norm_single]

/-- The rooted trace of a geometric corner is its actual area. This
does not assign counting measure to points of the base space. -/
theorem trace_corner (μ : Measure α) {s : Set α} (hs : MeasurableSet s) :
    trace μ (corner (G:=G) s)=μ s := by
  classical
  have he : (fun x => ENNReal.ofReal (matrix (corner (G:=G) s x) 1 1).re)=
      s.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x∈s <;> simp [corner_matrix,hx]
  rw [trace,he,lintegral_indicator hs]
  simp

/-- A uniformly bounded operator supported on the right in a geometric
corner has trace at most its norm bound times the area's measure. -/
theorem trace_le_corner (μ : Measure α) {s : Set α} (hs : MeasurableSet s)
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) {C : ℝ}
    (hB : ∀ x, ‖B x‖≤C) (hsupport : ∀ x, (B x).comp (corner s x)=B x) :
    trace μ B≤ENNReal.ofReal C*μ s := by
  classical
  calc
    trace μ B≤∫⁻ x,s.indicator (fun _ => ENNReal.ofReal C) x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x∈s
      · rw [Set.indicator_of_mem hx]
        apply ENNReal.ofReal_le_ofReal
        calc
          (matrix (B x) 1 1).re≤‖matrix (B x) 1 1‖ := Complex.re_le_norm _
          _ ≤ ‖B x‖*‖delta (1 : G)‖ :=
            (lp.norm_apply_le_norm (by norm_num) (B x (delta 1)) 1).trans ((B x).le_opNorm _)
          _ ≤ C := by simpa only [root_delta_norm,mul_one] using hB x
      · have he := congrArg (fun T : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) => T (delta 1)) (hsupport x)
        rw [comp_apply,corner_delta,one_smul,ite_eq_right hx,map_zero] at he
        simp [matrix,← he,hx]
    _ = ENNReal.ofReal C*μ s := by rw [lintegral_indicator hs]; simp

end Orbit

#print axioms operator_norm_le
#print axioms operator_adjoint
#print axioms unit_norm
#print axioms unit_adjoint_mul
#print axioms unit_mul_adjoint
#print axioms corner_covariant
#print axioms corner_idempotent
#print axioms corner_adjoint
#print axioms corner_positive
#print axioms trace_corner
#print axioms trace_le_corner

end AsymptoticOrbitDiagonal
