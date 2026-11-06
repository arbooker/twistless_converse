module

public import QuantitativeEulerEndpointWideGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeHolomorphic QuantitativeEulerDiamondDecode
open AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularBranchFamily AsymptoticCompactBranch
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- Actual right transport on a wide compact region, with explicit width
cost and no periodicity assumption on the transported vector. -/
theorem branchTransport_wide_norm (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {M : IntegerMatrix2} {B R H ε : ℝ}
    (hM : IntegerAction (ofMatrix b.matrix b.positive) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤R) (him : ∀ z∈s, z.im≤H) (t : ℕ) (x : ℍ) :
    ‖branchTransport b hs hε t x‖≤(wideDistortion B R H)^t := by
  apply branchTransport_norm_of_ratio b hs hε (pow_nonneg (wideDistortion_pos B R H).le t)
  intro z hz
  apply compact_ratio_le_of_height _ hε (le_max_left _ _) t z
  have hh := wide_integer_height_distortion hM hB hb z (hre z hz) (him z hz)
  rwa [ofMatrix_action] at hh

theorem compactAction_mul_symbol_wide_norm (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {M : IntegerMatrix2} {B R H ε : ℝ}
    (hM : IntegerAction (ofMatrix b.matrix b.positive) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤R) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (A : Ring) (v : Space) :
    ‖compactAction hs hε t x (A*symbol (ofMatrix b.matrix b.positive)) v‖≤
      (wideDistortion B R H)^t*
        ‖compactAction (branchImage_compact b hs) hε t x A v‖ := by
  rw [compactAction_mul_symbol,ContinuousLinearMap.comp_apply]
  exact (branchTransport b hs hε t x).le_of_opNorm_le
    (branchTransport_wide_norm b hs hM hB hb hε hre him t x) _

/-- All right multipliers with the same integral height use one common
rectangle, even when the source is wider than a unit strip. -/
theorem compact_right_wide_bound (g : G) {M : IntegerMatrix2} {B R Y H ε : ℝ}
    (hM : IntegerAction g M) (hB : 0≤B) (hb : MatrixEntryBound M B) (hY : 0<Y)
    (A : Ring) {s : Set ℍ} (hs : IsCompact s) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x (A*symbol g) v‖≤
      (wideDistortion B R H)^t*
        ‖compactAction (wideImageRegion_compact B R H hY) hε t x A v‖ := by
  let b := symbolBranch g
  have hMb : IntegerAction (ofMatrix b.matrix b.positive) M := by
    rw [symbolBranch_label]
    exact hM
  have ht := compactAction_mul_symbol_wide_norm b hs hMb hB hb hε hre him t x A v
  have he := congrArg (fun a : G => ‖compactAction hs hε t x (A*symbol a) v‖)
    (symbolBranch_label g)
  have hr := compactAction_restrict_norm A (branchImage_compact b hs)
    (wideImageRegion_compact B R H hY)
    (branchImage_subset_wide b hMb hB hb hY hre hlo him) hε t x v
  exact he.symm.trans_le (ht.trans (mul_le_mul_of_nonneg_left hr
    (pow_nonneg (wideDistortion_pos B R H).le t)))

#print axioms branchTransport_wide_norm
#print axioms compactAction_mul_symbol_wide_norm
#print axioms compact_right_wide_bound
end QuantitativeEulerEndpointPrepared
