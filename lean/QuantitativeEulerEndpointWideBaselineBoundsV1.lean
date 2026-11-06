module

public import QuantitativeEulerEndpointWidePacketBoundsV1
public import QuantitativeEulerEndpointBaselineInitializerV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticRegularObservationRows AsymptoticRegularBranchFamily
open AsymptoticCertificateBranches QuantitativeHolomorphic AsymptoticSectorSigns
open AsymptoticObservationStack AsymptoticPolarIsometry
open QuantitativeArithmetic QuantitativeEulerDensityGenerators
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

def wideRowBound (B R Y H : ℝ) (t : ℕ) : ℝ :=
  (2*(wideCompactCutoff B R Y H:ℝ)+1)*(wideDistortion B R H)^t

theorem wideRowBound_nonneg (B R Y H : ℝ) (t : ℕ) : 0≤wideRowBound B R Y H t :=
  mul_nonneg (by positivity) (pow_nonneg (wideDistortion_pos _ _ _).le _)

def wideTwistBound (N q : ℕ) (w : ℂ) (R Y H : ℝ) (t : ℕ) : ℝ :=
  2*(q:ℝ)*(1+‖w‖)*wideRowBound (N*q^3:ℕ) R Y H t

def wideRamifiedBound (p : ℕ) (δ : ℂ) (R Y H : ℝ) (t : ℕ) : ℝ :=
  ((p:ℝ)+1)*(1+‖δ‖)*wideRowBound p R Y H t

variable {s : Set ℍ} (hs : IsCompact s) {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
  (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H)

include hY hre hlo hhi in
theorem twist_wide_norm (N q : ℕ) (hN : 0<N) (hq : 0<q) (w : ℂ) (t : ℕ) (x : ℍ) :
    ‖twist N q hN hq w hs hε t x‖≤wideTwistBound N q w R Y H t := by
  choose M hM hB using twistBranches_integer_representatives N q hN hq
  have hf := family_wide_norm (twistBranches N q hN hq)
    (Sum.elim (fun _ => (1:ℂ)) (fun _ => -w)) hs M hM
    (show (0:ℝ)≤(N*q^3:ℕ) by positivity) hB hY hε hre hlo hhi t x
  exact hf.trans (mul_le_mul_of_nonneg_right (twist_coefficient_mass q w) (wideRowBound_nonneg _ _ _ _ _))

include hY hre hlo hhi in
theorem ramified_wide_norm (p : ℕ) (hp : 0<p) (δ : ℂ) (t : ℕ) (x : ℍ) :
    ‖bad p hp δ hs hε t x‖≤wideRamifiedBound p δ R Y H t := by
  choose M hM hB using ramifiedBranches_integer_representatives p hp
  have hf := family_wide_norm (ramifiedBranches p hp)
    (Sum.elim (fun _ => (1:ℂ)) (fun _ => -δ)) hs M hM
    (show (0:ℝ)≤p by positivity) hB hY hε hre hlo hhi t x
  have hc : (∑ i : Fin p ⊕ Unit, ‖(Sum.elim (fun _ => (1:ℂ)) (fun _ => -δ)) i‖)≤
      ((p:ℝ)+1)*(1+‖δ‖) := by
    have hi (i : Fin p ⊕ Unit) : ‖(Sum.elim (fun _ => (1:ℂ)) (fun _ => -δ)) i‖≤1+‖δ‖ := by
      cases i <;> simp only [Sum.elim_inl,Sum.elim_inr,norm_one,norm_neg] <;> linarith [norm_nonneg δ]
    calc
      _ ≤ ∑ _i : Fin p ⊕ Unit, (1+‖δ‖) := Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by simp; ring
  exact hf.trans (mul_le_mul_of_nonneg_right hc (wideRowBound_nonneg _ _ _ _ _))

def wideBaselineRowBound (N : ℕ) [NeZero N] (sector : Sector N) (R Y H : ℝ) (t : ℕ) : NewBaselineIndex N → ℝ
  | .inl none => wideTwistBound N 1 (sign sector.1) R Y H t
  | .inl (some a) => wideTwistBound N (primeLift N a).q (sign sector.1) R Y H t
  | .inr p => wideRamifiedBound p.val (AsymptoticCylinderRamified.eigenvalue sector p.val) R Y H t

theorem wideBaselineRowBound_nonneg (N : ℕ) [NeZero N] (sector : Sector N) (R Y H : ℝ)
    (t : ℕ) (i : NewBaselineIndex N) : 0≤wideBaselineRowBound N sector R Y H t i := by
  cases i with
  | inl i =>
    cases i <;> exact mul_nonneg (by positivity) (wideRowBound_nonneg _ _ _ _ _)
  | inr p => exact mul_nonneg (by positivity) (wideRowBound_nonneg _ _ _ _ _)

include hY hre hlo hhi in
theorem newBaselineRows_wide_norm (N : ℕ) [NeZero N] (sector : Sector N) (t : ℕ) (x : ℍ) (i : NewBaselineIndex N) :
    ‖newBaselineRows N sector hs hε t x i‖≤wideBaselineRowBound N sector R Y H t i := by
  cases i with
  | inl i =>
    cases i with
    | none => exact twist_wide_norm hs hε hY hre hlo hhi N 1 (NeZero.pos N) Nat.zero_lt_one (sign sector.1) t x
    | some a =>
      exact twist_wide_norm hs hε hY hre hlo hhi N (primeLift N a).q
        (NeZero.pos N) (primeLift N a).prime.pos (sign sector.1) t x
  | inr p =>
    exact ramified_wide_norm hs hε hY hre hlo hhi p.val
      (Nat.mem_primeFactors.mp p.property).1.pos (AsymptoticCylinderRamified.eigenvalue sector p.val) t x

def wideDetectorBound (N : ℕ) [NeZero N] (sector : Sector N) (R Y H : ℝ) (t : ℕ) : ℝ :=
  ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : NewBaselineIndex N => Space)).symm.toContinuousLinearMap‖*
    ∑ i, wideBaselineRowBound N sector R Y H t i

include hY hre hlo hhi in
/-- The initial detector also has explicit geometric bounds. Its square
root is handled by the exact stack norm identity. -/
theorem newBaselineDetector_wide_norm (N : ℕ) [NeZero N] (sector : Sector N) (t : ℕ) (x : ℍ) :
    ‖newBaselineDetector N sector hs hε t x‖≤wideDetectorBound N sector R Y H t := by
  rw [newBaselineDetector,absolute_opNorm]
  exact stack_norm_le _ _ (wideBaselineRowBound_nonneg N sector R Y H t)
    (newBaselineRows_wide_norm hs hε hY hre hlo hhi N sector t x)

#print axioms twist_wide_norm
#print axioms ramified_wide_norm
#print axioms newBaselineRows_wide_norm
#print axioms newBaselineDetector_wide_norm
end QuantitativeEulerEndpointPrepared
