module

public import QuantitativeHolomorphicUniformTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTraceMass
open MeasureTheory UpperHalfPlane AsymptoticUnweightedKernel AsymptoticFiniteBranch
open AsymptoticRegularTrace QuantitativeHolomorphic
open scoped Classical

/-- Remove a positive slack in a coefficient cap, including zero coefficients. -/
theorem cap_limit {x B E : ℝ} (hE : 0≤E) (h : ∀ η : ℝ,0<η → x≤(B+η)*E) : x≤B*E := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hden : 0<E+1 := by linarith
  have hη : 0<δ/(E+1) := div_pos hδ hden
  have hh := h (δ/(E+1)) hη
  have he : δ/(E+1)*(E+1)=δ := div_mul_cancel₀ _ hden.ne'
  nlinarith

/-- The branch comparison uses only its actual coefficient bound, with no
additive charge per branch. All geometry and periodization inputs are explicit. -/
theorem retained_branch_mass_trace_bound (b : Branch) {ε D Y H : ℝ}
    (hε : 0 < ε) (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H)
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H 1 ≤ 1 + |(n : ℝ)|)
    (geom : b.label ≠ 1 → RetainedBranchGeometry b Y H D S) :
    |liftedTrace h hε (holomorphic (retained Y H b) (h + 1)) / ((2 * h + 2 : ℕ) : ℝ) -
      signedTrace volume (regular (retained Y H b)) / (4 * Real.pi)| ≤
      b.bound * retainedBranchError b D Y H h S := by
  classical
  let := endpointRegion_finite hY H b
  by_cases hb : b.label = 1
  · simpa only [retainedBranchError,hb,ite_true] using retained_identity_trace_bound b hε hY hH hb h
  · let q := geom hb
    have hr : ∀ z ∈ endpointRegion Y H b,
        Y ≤ (b.label • z).im ∧ Y ≤ z.im ∧ (b.label • z).im ≤ H ∧ z.im ≤ H ∧
          |(b.label • z).re - z.re| ≤ 1 := by
      intro z hz
      refine ⟨hz.2.2.1, hz.1.2.1, hz.2.2.2.le, hz.1.2.2.le, ?_⟩
      have hs₁ : 0 ≤ z.re ∧ z.re < 1 := hz.1.1
      have hs₂ : 0 ≤ (b.label • z).re ∧ (b.label • z).re < 1 := hz.2.1
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hz : signedTrace volume (regular (retained Y H b)) = 0 := by
      change signedTrace volume (AsymptoticOrbitBranch.operator b.label
        ((endpointRegion Y H b).indicator b.coefficient) b.bound_nonneg
        (indicator_coefficient_bound _ _ b.bound_nonneg b.norm_le)) = 0
      rw [AsymptoticOrbitBranch.operator_signedTrace]
      simp only [hb, ite_false]
    rw [hz, zero_div, sub_zero]
    simp only [retainedBranchError, hb, ite_false]
    have herror : 0≤periodizedBranchError D Y H 1 (volume.real (endpointRegion Y H b)) h S.card/(4*Real.pi) := by
      have hK := QuantitativeHolomorphic.compactKernelBound_nonneg Y H 1
      unfold periodizedBranchError branchIntegralError
      positivity
    apply cap_limit herror
    intro η hη
    have hc : ∀ z,‖b.coefficient z‖≤b.bound+η := fun z => (b.norm_le z).trans (by linarith)
    have hi := retained_rational_operator_trace_bound_of_cap b.label q.a q.b' q.c q.d q.det_ne
      (endpointRegion Y H b) (endpointRegion_measurable Y H b) (isFiniteMeasure_restrict.mp inferInstance)
      (fun _ hz => hz.1.1) (fun _ hz => hz.2.1) b.coefficient
      (show 0 < b.bound + η by linarith [b.bound_nonneg]) b.measurable hc hD hY hH hε hr
      q.denominator_ne q.denominator_bound q.action_formula h hsmall S q.translated_nonidentity hfar
    exact hi.trans_eq (by ring)

/-- Quantitative finite-expression comparison, with summability of the
physical diagonals and integrability of the regular root already proved.
The only quantitative hypotheses concern matrix geometry and explicit
scalar error formulas. -/
theorem retained_expression_mass_trace_bound (e : Expression) {ε D Y H E : ℝ}
    (hε : 0 < ε) (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H)
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H 1 ≤ 1 + |(n : ℝ)|)
    (geom : ∀ b ∈ e, b.label ≠ 1 → RetainedBranchGeometry b Y H D S)
    (herr : ∀ b ∈ e, retainedBranchError b D Y H h S ≤ E) :
    |liftedTrace h hε (holomorphicSum (retainedExpression Y H e) (h + 1)) /
        ((2 * h + 2 : ℕ) : ℝ) -
      signedTrace volume (regularSum (retainedExpression Y H e)) / (4 * Real.pi)| ≤
      expressionBound e * E := by
  induction e with
  | nil =>
    simp [retainedExpression, holomorphicSum, regularSum, liftedTrace_eq_sum,
      signedTrace, matrix, expressionBound]
  | cons b e ih =>
    have ht := ih (fun c hc => geom c (List.mem_cons_of_mem b hc))
      (fun c hc => herr c (List.mem_cons_of_mem b hc))
    have hb := (retained_branch_mass_trace_bound b hε hD hY hH h hsmall S hfar
      (geom b List.mem_cons_self)).trans
      (mul_le_mul_of_nonneg_left (herr b List.mem_cons_self) b.bound_nonneg)
    have he : liftedTrace h hε (holomorphicSum (retainedExpression Y H (b :: e)) (h + 1)) =
        liftedTrace h hε (holomorphic (retained Y H b) (h + 1)) +
          liftedTrace h hε (holomorphicSum (retainedExpression Y H e) (h + 1)) :=
      liftedTrace_add h hε _ _ (retained_diagonal_summable h hε hY H b)
        (retainedExpression_diagonal_summable h hε hY H e)
    rw [he, retainedExpression_signedTrace_cons hY]
    rw [add_div, add_div, add_sub_add_comm]
    apply (abs_add_le _ _).trans
    apply (add_le_add hb ht).trans_eq
    simp only [expressionBound, List.map_cons, List.sum_cons]
    ring


theorem retained_expression_mass_uniform_trace_bound (e : Expression) {ε D Y H : ℝ}
    (hε : 0<ε) (hD : 0≤D) (hY : 0<Y) (hH : 0<H)
    (h : ℕ) (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*D≤1) (S : Finset ℤ)
    (hfar : ∀ n : ℤ,n∉S → 2*compactBaseBound Y H 1≤1+|(n:ℝ)|)
    (geom : ∀ b∈e,b.label≠1 → RetainedBranchGeometry b Y H D S) :
    |liftedTrace h hε (holomorphicSum (retainedExpression Y H e) (h+1))/(2*h+2:ℕ)-
      signedTrace volume (regularSum (retainedExpression Y H e))/(4*Real.pi)|≤
      expressionBound e*uniformRetainedTraceError D Y H h S.card :=
  retained_expression_mass_trace_bound e hε hD hY hH h hsmall S hfar geom
    (fun b _ => retainedBranchError_le_uniform b D hY H h S)

#print axioms retained_branch_mass_trace_bound
#print axioms retained_expression_mass_trace_bound
#print axioms retained_expression_mass_uniform_trace_bound
end QuantitativeEulerEndpointTraceMass
