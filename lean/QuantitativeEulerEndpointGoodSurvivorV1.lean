module

public import QuantitativeEulerEndpointSurvivorRegularV1
public import QuantitativeSpectralExceptionalGoodRootV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open QuantitativeSpectralObservability QuantitativeSpectralExceptionalGoodRoot
open scoped Classical ENNReal

/-- The actual compressed source with the invariant null set of bad roots removed. -/
def goodBaselineSurvivor (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) (x : ℍ) :
    Submodule ℂ Space := source N (fun y => baselineSurvivor N H w hs hε t y a) x

instance good_baseline_survivor_complete (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) (x : ℍ) :
    CompleteSpace (goodBaselineSurvivor N H w hs hε t a x) := by
  unfold goodBaselineSurvivor
  infer_instance

theorem good_baseline_survivor_regular (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) (ha : 0<a) :
    (∀ g h,Measurable (fun x => matrix (goodBaselineSurvivor N H w hs hε t a x).starProjection g h)) ∧
      Covariant (fun x => (goodBaselineSurvivor N H w hs hε t a x).starProjection) := by
  simp only [goodBaselineSurvivor,source_projection]
  exact family_regular N (NeZero.pos N) _ (baseline_survivor_regular N H w hs hε t a ha).1
    (baseline_survivor_regular N H w hs hε t a ha).2

theorem good_baseline_survivor_supported (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime]
    (hqN : ¬q∣N) (hqfixed : ∀ a : QuantitativeArithmetic.UnitResidue N,
      ¬q∣(QuantitativeEulerDensityGenerators.primeLift N a).q)
    (H : ℝ) (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (a : ℝ) (ha : 0<a) (x : ℍ) :
    Supported (integralGroup q) (goodBaselineSurvivor N H w hs hε t a x).starProjection := by
  simp only [goodBaselineSurvivor,source_projection]
  by_cases hx : fundamentalGood N x
  · simpa only [family,ite_eq_left hx] using
      baseline_survivor_supported N q hqN hqfixed H w hs hε t x a ha
  · simp only [family,ite_eq_right hx]
    intro g h hgh
    simp [matrix]

theorem good_baseline_survivor_trace (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) :
    trace volume (fun x => (goodBaselineSurvivor N H w hs hε t a x).starProjection)=
      trace volume (fun x => (baselineSurvivor N H w hs hε t x a).starProjection) :=
  source_trace N (NeZero.pos N) _

theorem good_baseline_survivor_trace_finite (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) :
    trace volume (fun x => (goodBaselineSurvivor N H w hs hε t a x).starProjection)<∞ := by
  rw [good_baseline_survivor_trace]
  exact baseline_survivor_trace_finite N H w hs hε t a

#print axioms good_baseline_survivor_regular
#print axioms good_baseline_survivor_supported
#print axioms good_baseline_survivor_trace
end QuantitativeEulerEndpointPrepared
