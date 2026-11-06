module

public import QuantitativeHolomorphicRetainedTraceV1
public import QuantitativeHolomorphicWordGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open MeasureTheory UpperHalfPlane AsymptoticUnweightedKernel AsymptoticFiniteBranch
open AsymptoticRegularTrace

/-- A common trace error for all branches in the same retained strip.
The terminal hyperbolic area is evaluated explicitly. -/
def uniformRetainedTraceError (D Y H : ℝ) (h : ℕ) (count : ℕ) : ℝ :=
  max (diagonalTraceError Y H Y⁻¹ h)
    (periodizedBranchError D Y H 1 Y⁻¹ h count / (4 * Real.pi))

theorem retained_endpoint_area_le (b : Branch) {Y : ℝ} (hY : 0 < Y) (H : ℝ) :
    volume.real (endpointRegion Y H b) ≤ Y⁻¹ := by
  have hs : endpointRegion Y H b ⊆ AsymptoticHyperbolicArea.closedTerminal Y :=
    fun _ hz => ⟨hz.1.1, hz.1.2.1⟩
  have hm : volume (endpointRegion Y H b) ≤ volume (AsymptoticHyperbolicArea.closedTerminal Y) := measure_mono hs
  rw [AsymptoticHyperbolicArea.closed_terminal_area hY] at hm
  have hr := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal Y⁻¹ ≠ ⊤) hm
  simpa only [Measure.real, ENNReal.toReal_ofReal (inv_nonneg.mpr hY.le)] using hr

theorem compactKernelBound_nonneg (Y H R : ℝ) : 0 ≤ compactKernelBound Y H R := by
  unfold compactKernelBound
  exact mul_nonneg (sq_nonneg _) (tsum_nonneg fun n => by unfold integerDecay; positivity)

theorem diagonalTraceError_mono_area (Y H : ℝ) (h : ℕ) {a A : ℝ} (ha : a ≤ A) :
    diagonalTraceError Y H a h ≤ diagonalTraceError Y H A h := by
  have hK := compactKernelBound_nonneg Y H 0
  unfold diagonalTraceError
  gcongr

theorem periodizedBranchError_mono_area (D Y H R : ℝ) (h count : ℕ)
    {a A : ℝ} (ha : a ≤ A) :
    periodizedBranchError D Y H R a h count ≤ periodizedBranchError D Y H R A h count := by
  have hK := compactKernelBound_nonneg Y H R
  unfold periodizedBranchError branchIntegralError
  gcongr

theorem retainedBranchError_le_uniform (b : Branch) (D : ℝ) {Y : ℝ} (hY : 0 < Y)
    (H : ℝ) (h : ℕ) (S : Finset ℤ) :
    retainedBranchError b D Y H h S ≤ uniformRetainedTraceError D Y H h S.card := by
  classical
  have ha := retained_endpoint_area_le b hY H
  unfold retainedBranchError uniformRetainedTraceError
  split_ifs
  · exact (diagonalTraceError_mono_area Y H h ha).trans (le_max_left _ _)
  · exact (div_le_div_of_nonneg_right
      (periodizedBranchError_mono_area D Y H 1 h S.card ha) (by positivity)).trans (le_max_right _ _)

/-- Concrete finite-expression comparison with no per-branch trace or
scalar error assumption.  The common error displays all weight, height,
area, and periodization-cutoff dependence. -/
theorem retained_expression_uniform_trace_bound (e : Expression) {ε D Y H : ℝ}
    (hε : 0 < ε) (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H)
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H 1 ≤ 1 + |(n : ℝ)|)
    (geom : ∀ b ∈ e, b.label ≠ 1 → RetainedBranchGeometry b Y H D S) :
    |liftedTrace h hε (holomorphicSum (retainedExpression Y H e) (h + 1)) /
        ((2 * h + 2 : ℕ) : ℝ) -
      signedTrace volume (regularSum (retainedExpression Y H e)) / (4 * Real.pi)| ≤
      (expressionBound e + (e.length : ℝ)) * uniformRetainedTraceError D Y H h S.card :=
  retained_expression_trace_bound e hε hD hY hH h hsmall S hfar geom
    (fun b _ => retainedBranchError_le_uniform b D hY H h S)

theorem retained_single_filter_uniform_trace_bound (e : Expression) (s : ℂ) (d : ℕ)
    {ε D Y H : ℝ} (hε : 0 < ε) (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H)
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H 1 ≤ 1 + |(n : ℝ)|)
    (geom : ∀ b ∈ powerExpression ([identity] ++ scaleExpression (-s) e) d,
      b.label ≠ 1 → RetainedBranchGeometry b Y H D S) :
    |liftedTrace h hε (holomorphicSum
        (retainedExpression Y H (powerExpression ([identity] ++ scaleExpression (-s) e) d)) (h + 1)) /
        ((2 * h + 2 : ℕ) : ℝ) -
      signedTrace volume (regularSum
        (retainedExpression Y H (powerExpression ([identity] ++ scaleExpression (-s) e) d))) /
        (4 * Real.pi)| ≤
      ((1 + ‖s‖ * expressionBound e) ^ d + ((1 + e.length : ℕ) : ℝ) ^ d) *
        uniformRetainedTraceError D Y H h S.card :=
  retained_single_filter_trace_bound e s d hε hD hY hH h hsmall S hfar geom
    (fun b _ => retainedBranchError_le_uniform b D hY H h S)

/-- Word-height bookkeeping supplies the denominator bound in the
geometric certificate from generator entry heights. -/
def retainedBranchGeometry_of_word (b : Branch) (Y H : ℝ) (S : Finset ℤ)
    (l : List IntegerMatrix2) {B : ℝ} (hB : 0 ≤ B)
    (hl : ∀ M ∈ l, MatrixEntryBound M B)
    (hdet : l.prod 0 0 * l.prod 1 1 - l.prod 0 1 * l.prod 1 0 ≠ 0)
    (hden : ∀ z ∈ endpointRegion Y H b, (l.prod 1 0 : ℂ) * (z : ℂ) + l.prod 1 1 ≠ 0)
    (hformula : ∀ z ∈ endpointRegion Y H b,
      ((b.label • z : ℍ) : ℂ) =
        ((l.prod 0 0 : ℂ) * (z : ℂ) + l.prod 0 1) / ((l.prod 1 0 : ℂ) * (z : ℂ) + l.prod 1 1))
    (hne : ∀ j ∈ S, l.prod 1 0 ≠ 0 ∨ l.prod 1 1 ≠ l.prod 0 0 + j * l.prod 1 0 ∨
      l.prod 0 1 + j * l.prod 1 1 ≠ 0) :
    RetainedBranchGeometry b Y H (((2 * B) ^ l.length) * (H + 2)) S where
  a := l.prod 0 0
  b' := l.prod 0 1
  c := l.prod 1 0
  d := l.prod 1 1
  det_ne := hdet
  denominator_ne := hden
  denominator_bound := by
    intro z hz
    apply strip_matrix_denominator_bound (by positivity) (matrix_entry_bound_word l hB hl) z
    · have hs : 0 ≤ z.re ∧ z.re < 1 := hz.1.1
      rw [abs_of_nonneg hs.1]
      exact hs.2.le
    · exact hz.1.2.2.le
  action_formula := hformula
  translated_nonidentity := hne

#print axioms retained_endpoint_area_le
#print axioms retained_expression_uniform_trace_bound
#print axioms retained_single_filter_uniform_trace_bound
#print axioms retainedBranchGeometry_of_word

end QuantitativeHolomorphic
