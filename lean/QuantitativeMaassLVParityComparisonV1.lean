module

public import QuantitativeMaassLVGeometricLowerV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- Opposite parity projections sum to the identity. -/
theorem parityProjection_add_neg (N : ℕ) (σ : ℝ) (v : AutomorphicSpace N) :
    parityProjection N σ v+parityProjection N (-σ) v=v := by
  rw [parityProjection_apply,parityProjection_apply,Complex.ofReal_neg]
  module

/-- For an insertion commuting with parity, the projected quadratic form is
its projected first-slot pairing with the original vector. -/
theorem parityProjection_commuting_quadratic (N : ℕ) (σ : ℝ) (hσ : σ^2=1)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hA : Commute (parityProjection N σ) A) (v : AutomorphicSpace N) :
    inner ℂ (A (parityProjection N σ v)) (parityProjection N σ v)=
      inner ℂ (A (parityProjection N σ v)) v := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (parityProjection_selfAdjoint N σ)
  have hh : parityProjection N σ (A (parityProjection N σ v))=A (parityProjection N σ v) := by
    have hc := DFunLike.congr_fun hA.eq (parityProjection N σ v)
    change parityProjection N σ (A (parityProjection N σ v))=A (parityProjection N σ (parityProjection N σ v)) at hc
    rwa [parityProjection_idempotent N σ hσ] at hc
  exact (hs (A (parityProjection N σ v)) v).symm.trans (congrArg (fun w => inner ℂ w v) hh)

/-- The actual LV quadratic form splits exactly into its two parity pieces. -/
theorem actualLVFilter_parity_split (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ)
    (σ : ℝ) (hσ : σ^2=1) (v : AutomorphicSpace N) :
    inner ℂ (actualLVFilter N p hN hpN a b hab d v) v=
      inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N σ v)) (parityProjection N σ v)+
      inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N (-σ) v)) (parityProjection N (-σ) v) := by
  have hcomm (s : ℝ) := parityProjection_commute N s _
    (reflectionIsometry_actualLVFilter_commute N p hN hpN hNp a b hab d)
  rw [parityProjection_commuting_quadratic N σ hσ _ (hcomm σ),
    parityProjection_commuting_quadratic N (-σ) (by simpa only [neg_sq] using hσ) _ (hcomm (-σ)),
    ← inner_add_left,← map_add,parityProjection_add_neg]

/-- Losing the opposite parity costs at most its unfiltered projection energy.
Thus a full LV lower bound and an unfiltered opposite-parity upper bound imply
the desired parity lower bound without reflected Hecke-word geometry. -/
theorem actualLVFilter_parity_lower (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ)
    (σ : ℝ) (hσ : σ^2=1) (v : AutomorphicSpace N) :
    (inner ℂ (actualLVFilter N p hN hpN a b hab d v) v).re-
      ‖parityProjection N (-σ) v‖^2≤
    (inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N σ v)) (parityProjection N σ v)).re := by
  let A := actualLVFilter N p hN hpN a b hab d
  let w := parityProjection N (-σ) v
  have hn : ‖A w‖≤‖w‖ := by
    calc
      ‖A w‖ ≤ ‖A‖*‖w‖ := A.le_opNorm w
      _ ≤ 1*‖w‖ := mul_le_mul_of_nonneg_right (actualLVFilter_order N p hN hpN a b hab d).2.2 (norm_nonneg w)
      _ = _ := one_mul _
  have hb : (inner ℂ (A w) w).re≤‖w‖^2 := by
    calc
      _ ≤ ‖inner ℂ (A w) w‖ := Complex.re_le_norm _
      _ ≤ ‖A w‖*‖w‖ := norm_inner_le_norm _ _
      _ ≤ ‖w‖*‖w‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg w)
      _ = _ := (pow_two _).symm
  have hh := congrArg Complex.re (actualLVFilter_parity_split N p hN hpN hNp a b hab d σ hσ v)
  rw [Complex.add_re] at hh
  change (inner ℂ (A v) v).re=(inner ℂ (A (parityProjection N σ v)) (parityProjection N σ v)).re+
    (inner ℂ (A w) w).re at hh
  change (inner ℂ (A v) v).re-‖w‖^2≤_
  linarith

#print axioms parityProjection_add_neg
#print axioms parityProjection_commuting_quadratic
#print axioms actualLVFilter_parity_split
#print axioms actualLVFilter_parity_lower

end QuantitativeMaass
