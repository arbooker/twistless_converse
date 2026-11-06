module

public import QuantitativeEulerEndpointNewBaselineV1
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

theorem newBaselineSurvivor_regular (N : ℕ) [NeZero N] (H : ℝ) (sector : AsymptoticSectorSigns.Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) (ha : 0<a) :
    (∀ g h,Measurable (fun x => matrix (newBaselineSurvivor N H sector hs hε t a x).starProjection g h)) ∧
      Covariant (fun x => (newBaselineSurvivor N H sector hs hε t a x).starProjection) := by
  have hU : (∀ g h,Measurable (fun x =>
      matrix (AsymptoticOrbitRegion.Space (G := AsymptoticRationalGroup.Group)
        (terminal ε\terminal H) x).starProjection g h)) ∧
      Covariant (fun x => (AsymptoticOrbitRegion.Space (G := AsymptoticRationalGroup.Group)
        (terminal ε\terminal H) x).starProjection) := by
    simp only [region_projection]
    exact ⟨corner_matrix_measurable (fun g => (AsymptoticRationalGroup.measurePreserving g).measurable)
      ((terminal_measurable ε).diff (terminal_measurable H)),corner_covariant _⟩
  obtain ⟨M,_hM,hM,hm,hc⟩ := newBaselineDetector_regular N sector hs hε t
  exact (step_regular _ _ hU.1 hU.2 hm hc M hM (Real.sqrt a) (Real.sqrt_pos.mpr ha)).1

theorem newBaselineSurvivor_supported (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime]
    (hqN : ¬q∣N) (hqfixed : ∀ a : QuantitativeArithmetic.UnitResidue N,
      ¬q∣(QuantitativeEulerDensityGenerators.primeLift N a).q)
    (H : ℝ) (sector : AsymptoticSectorSigns.Sector N) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (a : ℝ) (ha : 0<a) :
    Supported (integralGroup q) (newBaselineSurvivor N H sector hs hε t a x).starProjection := by
  apply (step_supported _ _ _ _
    (newBaselineDetector_supported N sector q hqN hqfixed hs hε t x)
    (Real.sqrt a) (Real.sqrt_pos.mpr ha)).1
  rw [region_projection]
  exact supported_corner _ _ _

theorem newBaselineSurvivor_trace_le (N : ℕ) [NeZero N] (H : ℝ) (sector : AsymptoticSectorSigns.Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) :
    trace volume (fun x => (newBaselineSurvivor N H sector hs hε t a x).starProjection)≤
      volume (terminal ε\terminal H) := by
  calc
    _ ≤ trace volume (fun x => (AsymptoticOrbitRegion.Space
        (G := AsymptoticRationalGroup.Group) (terminal ε\terminal H) x).starProjection) :=
      projection_trace_mono volume _ _ (fun _x => nextSpace_le _ _ _)
    _ = _ := by
      simp only [region_projection]
      exact trace_corner volume ((terminal_measurable ε).diff (terminal_measurable H))

theorem newBaselineSurvivor_trace_finite (N : ℕ) [NeZero N] (H : ℝ) (sector : AsymptoticSectorSigns.Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) :
    trace volume (fun x => (newBaselineSurvivor N H sector hs hε t a x).starProjection)<∞ := by
  apply (newBaselineSurvivor_trace_le N H sector hs hε t a).trans_lt
  apply (measure_mono Set.sdiff_subset).trans_lt
  rw [terminal_area hε]
  exact ENNReal.ofReal_lt_top

#print axioms newBaselineSurvivor_regular
#print axioms newBaselineSurvivor_supported
#print axioms newBaselineSurvivor_trace_le
#print axioms newBaselineSurvivor_trace_finite
end QuantitativeEulerEndpointPrepared
