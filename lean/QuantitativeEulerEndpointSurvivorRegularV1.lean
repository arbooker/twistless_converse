module

public import QuantitativeEulerEndpointBaselineRegularV1
public import QuantitativeEulerEndpointBaselineSurvivorV1
public import QuantitativeSpectralRegularCornerStepV1
public import QuantitativeSpectralExceptionalRowsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticHyperbolicArea
open AsymptoticRegularTrace AsymptoticPolarIsometry AsymptoticOrbitDiagonal
open QuantitativeSpectralCornerCutRow QuantitativeSpectralRegularCornerStep
open QuantitativeSpectralExceptionalRows AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal

instance baseline_survivor_complete (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (a : ℝ) :
    CompleteSpace (baselineSurvivor N H w hs hε t x a) := by
  unfold baselineSurvivor
  infer_instance

theorem baseline_survivor_regular (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) (ha : 0<a) :
    (∀ g h,Measurable (fun x => matrix (baselineSurvivor N H w hs hε t x a).starProjection g h)) ∧
      Covariant (fun x => (baselineSurvivor N H w hs hε t x a).starProjection) := by
  have hU : (∀ g h,Measurable (fun x =>
      matrix (AsymptoticOrbitRegion.Space (G := AsymptoticRationalGroup.Group)
        (terminal ε\terminal H) x).starProjection g h)) ∧
      Covariant (fun x => (AsymptoticOrbitRegion.Space (G := AsymptoticRationalGroup.Group)
        (terminal ε\terminal H) x).starProjection) := by
    simp only [region_projection]
    exact ⟨corner_matrix_measurable (fun g => (AsymptoticRationalGroup.measurePreserving g).measurable)
      ((terminal_measurable ε).diff (terminal_measurable H)),corner_covariant _⟩
  have hB := baseline_absolute_regular N w hs hε t
  exact (step_regular _ _ hU.1 hU.2 hB.1 hB.2 (baselineStackBound N w hs hε t)
    (fun x => by rw [absolute_opNorm]; exact baseline_stack_norm N w hs hε t x)
    (Real.sqrt a) (Real.sqrt_pos.mpr ha)).1

theorem baseline_survivor_supported (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime]
    (hqN : ¬q∣N) (hqfixed : ∀ a : QuantitativeArithmetic.UnitResidue N,
      ¬q∣(QuantitativeEulerDensityGenerators.primeLift N a).q)
    (H : ℝ) (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (a : ℝ) (ha : 0<a) :
    Supported (integralGroup q) (baselineSurvivor N H w hs hε t x a).starProjection := by
  apply (step_supported _ _ _ _
    (baseline_absolute_supported N q hqN hqfixed w hs hε t x)
    (Real.sqrt a) (Real.sqrt_pos.mpr ha)).1
  rw [region_projection]
  exact supported_corner _ _ _

theorem baseline_survivor_trace_le (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) :
    trace volume (fun x => (baselineSurvivor N H w hs hε t x a).starProjection)≤
      volume (terminal ε\terminal H) := by
  calc
    _ ≤ trace volume (fun x => (AsymptoticOrbitRegion.Space
        (G := AsymptoticRationalGroup.Group) (terminal ε\terminal H) x).starProjection) :=
      projection_trace_mono volume _ _ (fun x => baseline_survivor_le_band N H w hs hε t x a)
    _ = _ := by
      simp only [region_projection]
      exact trace_corner volume ((terminal_measurable ε).diff (terminal_measurable H))

theorem baseline_survivor_trace_finite (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) :
    trace volume (fun x => (baselineSurvivor N H w hs hε t x a).starProjection)<∞ := by
  apply (baseline_survivor_trace_le N H w hs hε t a).trans_lt
  apply (measure_mono Set.sdiff_subset).trans_lt
  rw [terminal_area hε]
  exact ENNReal.ofReal_lt_top

#print axioms baseline_survivor_regular
#print axioms baseline_survivor_supported
#print axioms baseline_survivor_trace_le
#print axioms baseline_survivor_trace_finite
end QuantitativeEulerEndpointPrepared
