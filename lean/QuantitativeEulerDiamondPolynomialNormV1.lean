module

public import QuantitativeEulerDiamondTransportV1
public import QuantitativeHolomorphicIntegerCompactV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondDecode

open UpperHalfPlane AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularBranchFamily AsymptoticCompactBranch QuantitativeHolomorphic
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- The operator defined using compactness-selected data satisfies any
proved coefficient bound; its norm is independent of that choice of data. -/
theorem branchTransport_norm_of_ratio (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {ε C : ℝ} (hε : 0<ε) (hC : 0≤C) (t : ℕ) (x : ℍ)
    (hc : ∀ z∈s, ratio (realMatrix b.matrix) ε t z≤C) :
    ‖branchTransport b hs hε t x‖≤C := by
  have hbound (z : ℍ) : ‖coefficient (realMatrix b.matrix) s ε t z‖≤C := by
    by_cases hz : z∈s
    · rw [coefficient,Set.indicator_of_mem hz,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (ratio_pos _ hε t z)]
      exact hc z hz
    · rw [coefficient,Set.indicator_of_notMem hz,norm_zero]
      exact hC
  let T := AsymptoticOrbitBranch.operator (ofMatrix b.matrix b.positive)
    (coefficient (realMatrix b.matrix) s ε t) hC hbound x
  have he : branchTransport b hs hε t x=T := by
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext a
    rfl
  rw [he]
  exact AsymptoticOrbitBranch.operator_norm_le _ _ hC hbound x

/-- A polynomial transport bound on the retained unit strip. In particular,
it has no dependence on the lower height cutoff or on epsilon. -/
theorem branchTransport_integer_norm (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {M : IntegerMatrix2} {B H ε : ℝ}
    (hM : IntegerAction (ofMatrix b.matrix b.positive) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (him : ∀ z∈s, z.im≤H) (t : ℕ) (x : ℍ) :
    ‖branchTransport b hs hε t x‖≤(integerCompactDistortion B H)^t := by
  apply branchTransport_norm_of_ratio b hs hε (by unfold integerCompactDistortion; positivity)
  intro z hz
  apply compact_ratio_le_of_height _ hε (le_max_left _ _) t z
  have hh := hM.height_distortion hB hb z (hre z hz) (him z hz)
  rw [ofMatrix_action] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (realMatrix b.matrix • z).im_pos.le)

theorem compactAction_mul_symbol_integer_norm (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {M : IntegerMatrix2} {B H ε : ℝ}
    (hM : IntegerAction (ofMatrix b.matrix b.positive) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (A : Ring) (v : Space) :
    ‖compactAction hs hε t x (A*symbol (ofMatrix b.matrix b.positive)) v‖≤
      (integerCompactDistortion B H)^t*
        ‖compactAction (branchImage_compact b hs) hε t x A v‖ := by
  rw [compactAction_mul_symbol,ContinuousLinearMap.comp_apply]
  exact (branchTransport b hs hε t x).le_of_opNorm_le
    (branchTransport_integer_norm b hs hM hB hb hε hre him t x) _

#print axioms branchTransport_norm_of_ratio
#print axioms branchTransport_integer_norm
#print axioms compactAction_mul_symbol_integer_norm
end QuantitativeEulerDiamondDecode
