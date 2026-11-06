module

public import QuantitativeEulerEndpointFundamentalTerminalV1
public import QuantitativeSpectralCutV1
public import QuantitativeSpectralExceptionalSourceObservabilityV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane ContinuousLinearMap QuantitativeEulerDensityGenerators
open QuantitativeArithmetic
open AsymptoticRegularObservationRows AsymptoticObservationStack
open AsymptoticRegularCompactBranch (Space)
open scoped Classical InnerProduct

def baselineRows (N : ℕ) [NeZero N] (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) : Option (UnitResidue N) → Space →L[ℂ] Space
  | none => twist N 1 (NeZero.pos N) Nat.zero_lt_one w hs hε t x
  | some a => twist N (primeLift N a).q (NeZero.pos N) (primeLift N a).prime.pos w hs hε t x

def baselineStack (N : ℕ) [NeZero N] (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) := stack (baselineRows N w hs hε t x)

theorem baselineStack_norm_sq (N : ℕ) [NeZero N] (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖baselineStack N w hs hε t x v‖^2=
      ‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w hs hε t x v‖^2+
      ‖fixedPrimeStack N w hs hε t x v‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2,Fintype.sum_option,PiLp.norm_sq_eq_of_L2]
  rfl

def baselineLowSpace (N : ℕ) [NeZero N] (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (a : ℝ) : Submodule ℂ Space :=
  let T := baselineStack N w hs hε t x
  QuantitativeSpectralCut.lowAt (T.adjoint.comp T) a

theorem baseline_low_energy (N : ℕ) [NeZero N] (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (a : ℝ) (v : Space)
    (hv : v∈baselineLowSpace N w hs hε t x a) :
    ‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w hs hε t x v‖^2+
      ‖fixedPrimeStack N w hs hε t x v‖^2≤a*‖v‖^2 := by
  let T := baselineStack N w hs hε t x
  have hT : IsSelfAdjoint (T.adjoint.comp T) := by
    rw [isSelfAdjoint_iff']
    simp only [adjoint_comp,adjoint_adjoint]
  have h := QuantitativeSpectralCut.quadratic_le_on_lowAt (T.adjoint.comp T) hT a hv
  rw [comp_apply,adjoint_inner_left] at h
  have hquad : (inner ℂ (T v) (T v)).re=‖T v‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (T v)).symm
  rw [hquad] at h
  exact (baselineStack_norm_sq N w hs hε t x v).symm.trans_le h

theorem baseline_threshold_pos (R : ℝ) (hR : 0≤R) : 0<(2*(1+R))⁻¹ := by positivity

theorem baseline_threshold_small (R : ℝ) (hR : 0≤R) : R*(2*(1+R))⁻¹≤1/2 := by
  rw [←div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*(1+R))).2
  linarith

#print axioms baselineStack_norm_sq
#print axioms baseline_low_energy
#print axioms baseline_threshold_small
end QuantitativeEulerEndpointPrepared
