module

public import QuantitativeHolomorphicConcreteTraceV1
public import QuantitativeHolomorphicDiagonalTraceV1
public import QuantitativeHolomorphicExpressionV1
public import AsymptoticFiniteExpressionTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open MeasureTheory UpperHalfPlane AsymptoticUnweightedKernel AsymptoticFiniteBranch
open AsymptoticRegularTrace
attribute [local instance] Classical.propDecidable

/-- Arithmetic and geometric data for a retained nonreturning branch.
There is no trace or convergence assumption in this certificate. -/
structure RetainedBranchGeometry (b : Branch) (Y H D : ℝ) (S : Finset ℤ) where
  a : ℤ
  b' : ℤ
  c : ℤ
  d : ℤ
  det_ne : a * d - b' * c ≠ 0
  denominator_ne : ∀ z ∈ endpointRegion Y H b, (c : ℂ) * (z : ℂ) + d ≠ 0
  denominator_bound : ∀ z ∈ endpointRegion Y H b, ‖(c : ℂ) * (z : ℂ) + d‖ ≤ D
  action_formula : ∀ z ∈ endpointRegion Y H b,
    ((b.label • z : ℍ) : ℂ) = ((a : ℂ) * (z : ℂ) + b') / ((c : ℂ) * (z : ℂ) + d)
  translated_nonidentity : ∀ j ∈ S, c ≠ 0 ∨ d ≠ a + j * c ∨ b' + j * d ≠ 0

def retainedBranchError (b : Branch) (D Y H : ℝ) (h : ℕ) (S : Finset ℤ) : ℝ :=
  if b.label = 1 then diagonalTraceError Y H (volume.real (endpointRegion Y H b)) h
  else periodizedBranchError D Y H 1 (volume.real (endpointRegion Y H b)) h S.card / (4 * Real.pi)

theorem retained_signedTrace_identity (b : Branch) {Y : ℝ} (hY : 0 < Y) (H : ℝ)
    (hb : b.label = 1) :
    signedTrace volume (regular (retained Y H b)) = (∫ z in endpointRegion Y H b, b.coefficient z).re := by
  classical
  let := endpointRegion_finite hY H b
  change signedTrace volume (AsymptoticOrbitBranch.operator b.label
    ((endpointRegion Y H b).indicator b.coefficient) b.bound_nonneg
    (indicator_coefficient_bound _ _ b.bound_nonneg b.norm_le)) = _
  rw [AsymptoticOrbitBranch.operator_signedTrace]
  simp only [hb, ite_true]
  have hi : Integrable b.coefficient (volume.restrict (endpointRegion Y H b)) :=
    (integrable_const b.bound).mono' b.measurable.aestronglyMeasurable (Filter.Eventually.of_forall b.norm_le)
  have he : (fun z => ((endpointRegion Y H b).indicator b.coefficient z).re) =
      (endpointRegion Y H b).indicator (fun z => (b.coefficient z).re) := by
    funext z
    by_cases hz : z ∈ endpointRegion Y H b <;> simp [hz]
  rw [he, integral_indicator (endpointRegion_measurable Y H b)]
  exact integral_re hi

theorem retained_identity_trace_bound (b : Branch) {ε Y H : ℝ}
    (hε : 0 < ε) (hY : 0 < Y) (hH : 0 < H) (hb : b.label = 1) (h : ℕ) :
    |liftedTrace h hε (holomorphic (retained Y H b) (h + 1)) / ((2 * h + 2 : ℕ) : ℝ) -
      signedTrace volume (regular (retained Y H b)) / (4 * Real.pi)| ≤
      b.bound * diagonalTraceError Y H (volume.real (endpointRegion Y H b)) h := by
  let := endpointRegion_finite hY H b
  rw [retained_signedTrace_identity b hY H hb]
  apply normalized_identity_branch_trace_bound_of_cap (endpointRegion Y H b)
    (endpointRegion_measurable Y H b) (isFiniteMeasure_restrict.mp inferInstance)
    (fun _ hz => hz.1.1) b.coefficient b.measurable.aestronglyMeasurable b.bound_nonneg
    (Filter.Eventually.of_forall b.norm_le) hY hH hε
    ((ae_restrict_mem (endpointRegion_measurable Y H b)).mono fun _ hz => ⟨hz.1.2.1, hz.1.2.2.le⟩)
    h
  intro n
  have hm := AsymptoticConcreteRationalBranch.retained_operator_mode b.label (endpointRegion Y H b)
    (endpointRegion_measurable Y H b) (fun _ hz => hz.2.1) b.coefficient b.measurable
    b.bound_nonneg b.norm_le h n hε
  simpa only [holomorphic, retained, hb, one_smul, AsymptoticSlashGauge.phase_one, mul_one] using hm

/-- The quantitative trace comparison for one literal retained branch.
The extra unit in the cap handles zero coefficients uniformly. -/
theorem retained_branch_trace_bound (b : Branch) {ε D Y H : ℝ}
    (hε : 0 < ε) (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H)
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H 1 ≤ 1 + |(n : ℝ)|)
    (geom : b.label ≠ 1 → RetainedBranchGeometry b Y H D S) :
    |liftedTrace h hε (holomorphic (retained Y H b) (h + 1)) / ((2 * h + 2 : ℕ) : ℝ) -
      signedTrace volume (regular (retained Y H b)) / (4 * Real.pi)| ≤
      (b.bound + 1) * retainedBranchError b D Y H h S := by
  classical
  let := endpointRegion_finite hY H b
  by_cases hb : b.label = 1
  · have hi := retained_identity_trace_bound b hε hY hH hb h
    simp only [retainedBranchError, hb, ite_true]
    apply hi.trans
    apply mul_le_mul_of_nonneg_right (by linarith)
    have hK : 0 ≤ compactKernelBound Y H 0 := by
      unfold compactKernelBound
      exact mul_nonneg (sq_nonneg _) (tsum_nonneg fun n => by unfold integerDecay; positivity)
    unfold diagonalTraceError
    positivity
  · let q := geom hb
    have hc : ∀ z, ‖b.coefficient z‖ ≤ b.bound + 1 := fun z => (b.norm_le z).trans (by linarith)
    have hr : ∀ z ∈ endpointRegion Y H b,
        Y ≤ (b.label • z).im ∧ Y ≤ z.im ∧ (b.label • z).im ≤ H ∧ z.im ≤ H ∧
          |(b.label • z).re - z.re| ≤ 1 := by
      intro z hz
      refine ⟨hz.2.2.1, hz.1.2.1, hz.2.2.2.le, hz.1.2.2.le, ?_⟩
      have hs₁ : 0 ≤ z.re ∧ z.re < 1 := hz.1.1
      have hs₂ : 0 ≤ (b.label • z).re ∧ (b.label • z).re < 1 := hz.2.1
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hi := retained_rational_operator_trace_bound_of_cap b.label q.a q.b' q.c q.d q.det_ne
      (endpointRegion Y H b) (endpointRegion_measurable Y H b) (isFiniteMeasure_restrict.mp inferInstance)
      (fun _ hz => hz.1.1) (fun _ hz => hz.2.1) b.coefficient
      (show 0 < b.bound + 1 by linarith [b.bound_nonneg]) b.measurable hc hD hY hH hε hr
      q.denominator_ne q.denominator_bound q.action_formula h hsmall S q.translated_nonidentity hfar
    have hz : signedTrace volume (regular (retained Y H b)) = 0 := by
      change signedTrace volume (AsymptoticOrbitBranch.operator b.label
        ((endpointRegion Y H b).indicator b.coefficient) b.bound_nonneg
        (indicator_coefficient_bound _ _ b.bound_nonneg b.norm_le)) = 0
      rw [AsymptoticOrbitBranch.operator_signedTrace]
      simp only [hb, ite_false]
    rw [hz, zero_div, sub_zero]
    simp only [retainedBranchError, hb, ite_false]
    exact hi.trans_eq (by ring)

/-- Quantitative finite-expression comparison, with summability of the
physical diagonals and integrability of the regular root already proved.
The only quantitative hypotheses concern matrix geometry and explicit
scalar error formulas. -/
theorem retained_expression_trace_bound (e : Expression) {ε D Y H E : ℝ}
    (hε : 0 < ε) (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H)
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H 1 ≤ 1 + |(n : ℝ)|)
    (geom : ∀ b ∈ e, b.label ≠ 1 → RetainedBranchGeometry b Y H D S)
    (herr : ∀ b ∈ e, retainedBranchError b D Y H h S ≤ E) :
    |liftedTrace h hε (holomorphicSum (retainedExpression Y H e) (h + 1)) /
        ((2 * h + 2 : ℕ) : ℝ) -
      signedTrace volume (regularSum (retainedExpression Y H e)) / (4 * Real.pi)| ≤
      (expressionBound e + (e.length : ℝ)) * E := by
  induction e with
  | nil =>
    simp [retainedExpression, holomorphicSum, regularSum, liftedTrace_eq_sum,
      signedTrace, matrix, expressionBound]
  | cons b e ih =>
    have ht := ih (fun c hc => geom c (List.mem_cons_of_mem b hc))
      (fun c hc => herr c (List.mem_cons_of_mem b hc))
    have hb := (retained_branch_trace_bound b hε hD hY hH h hsmall S hfar
      (geom b List.mem_cons_self)).trans
      (mul_le_mul_of_nonneg_left (herr b List.mem_cons_self) (by linarith [b.bound_nonneg]))
    have he : liftedTrace h hε (holomorphicSum (retainedExpression Y H (b :: e)) (h + 1)) =
        liftedTrace h hε (holomorphic (retained Y H b) (h + 1)) +
          liftedTrace h hε (holomorphicSum (retainedExpression Y H e) (h + 1)) :=
      liftedTrace_add h hε _ _ (retained_diagonal_summable h hε hY H b)
        (retainedExpression_diagonal_summable h hε hY H e)
    rw [he, retainedExpression_signedTrace_cons hY]
    rw [add_div, add_div, add_sub_add_comm]
    apply (abs_add_le _ _).trans
    apply (add_le_add hb ht).trans_eq
    simp only [expressionBound, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- The preceding bound applied to the actual single-filter polynomial.
Both coefficient mass and branch count are computed, not postulated. -/
theorem retained_single_filter_trace_bound (e : Expression) (s : ℂ) (d : ℕ)
    {ε D Y H E : ℝ} (hε : 0 < ε) (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H)
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H 1 ≤ 1 + |(n : ℝ)|)
    (geom : ∀ b ∈ powerExpression ([identity] ++ scaleExpression (-s) e) d,
      b.label ≠ 1 → RetainedBranchGeometry b Y H D S)
    (herr : ∀ b ∈ powerExpression ([identity] ++ scaleExpression (-s) e) d,
      retainedBranchError b D Y H h S ≤ E) :
    |liftedTrace h hε (holomorphicSum
        (retainedExpression Y H (powerExpression ([identity] ++ scaleExpression (-s) e) d)) (h + 1)) /
        ((2 * h + 2 : ℕ) : ℝ) -
      signedTrace volume (regularSum
        (retainedExpression Y H (powerExpression ([identity] ++ scaleExpression (-s) e) d))) /
        (4 * Real.pi)| ≤
      ((1 + ‖s‖ * expressionBound e) ^ d + ((1 + e.length : ℕ) : ℝ) ^ d) * E := by
  have hc := single_filter_expression_complexity e s d
  have hi := retained_expression_trace_bound
    (powerExpression ([identity] ++ scaleExpression (-s) e) d)
    hε hD hY hH h hsmall S hfar geom herr
  simpa only [hc.1, hc.2, Nat.cast_pow] using hi

#print axioms retained_expression_trace_bound
#print axioms retained_single_filter_trace_bound

#print axioms retained_identity_trace_bound
#print axioms retained_branch_trace_bound

end QuantitativeHolomorphic
