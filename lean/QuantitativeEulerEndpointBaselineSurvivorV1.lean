module

public import QuantitativeEulerEndpointLowSourceV1
public import AsymptoticPolarIsometryV1
public import QuantitativeSpectralCornerCutRowV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane ContinuousLinearMap AsymptoticHyperbolicArea
open AsymptoticPolarIsometry QuantitativeSpectralCornerCutRow
open AsymptoticRegularCompactBranch (Space)
open scoped Classical InnerProduct

/-- The standard compressed spectral deflation of the terminal band by
the absolute value of the actual fixed original-row stack. Its projection
has the existing exact subtraction formula for nextSpace. -/
def baselineSurvivor (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (a : ℝ) :
    Submodule ℂ Space :=
  nextSpace (AsymptoticOrbitRegion.Space (terminal ε\terminal H) x)
    (absolute (baselineStack N w hs hε t x)) (Real.sqrt a)

theorem baseline_survivor_le_band (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (a : ℝ) :
    baselineSurvivor N H w hs hε t x a≤AsymptoticOrbitRegion.Space (terminal ε\terminal H) x :=
  nextSpace_le _ _ _

theorem baseline_survivor_energy (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ)
    (a : ℝ) (ha : 0≤a) (v : Space) (hv : v∈baselineSurvivor N H w hs hε t x a) :
    ‖AsymptoticRegularObservationRows.twist N 1 (NeZero.pos N) Nat.zero_lt_one w hs hε t x v‖^2+
      ‖fixedPrimeStack N w hs hε t x v‖^2≤a*‖v‖^2 := by
  let U : Submodule ℂ Space := AsymptoticOrbitRegion.Space (terminal ε\terminal H) x
  let T := absolute (baselineStack N w hs hε t x)
  have hp : v∈U := nextSpace_le U T (Real.sqrt a) hv
  have he : restricted U T v=T v := by
    change T (U.starProjection v)=T v
    rw [U.starProjection_eq_self_iff.mpr hp]
  have hl := QuantitativeSpectralCut.quadratic_le_on_lowAt _
    (IsSelfAdjoint.star_mul_self (restricted U T)) ((Real.sqrt a)^2)
    (nextSpace_low U T (Real.sqrt a) hv)
  change (inner ℂ (((restricted U T).adjoint.comp (restricted U T)) v) v).re≤_ at hl
  rw [comp_apply,adjoint_inner_left] at hl
  have hquad : (inner ℂ (restricted U T v) (restricted U T v)).re=‖restricted U T v‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (restricted U T v)).symm
  rw [hquad,he,Real.sq_sqrt ha] at hl
  have heNorm : ‖baselineStack N w hs hε t x v‖=‖T v‖ := absolute_norm _ v
  rw [←heNorm] at hl
  exact (baselineStack_norm_sq N w hs hε t x v).symm.trans_le hl

#print axioms baseline_survivor_le_band
#print axioms baseline_survivor_energy
end QuantitativeEulerEndpointPrepared
