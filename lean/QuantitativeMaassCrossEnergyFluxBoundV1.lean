module

public import QuantitativeMaassCrossEnergyFluxV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass

/-- The local derivative multiplier has exactly the supplied gradient bound. -/
theorem crossLocalCutoffGradient_norm_le (K : Set ℍ) (hK : MeasurableSet K)
    (b : SmoothUpperSeed) (C : ℝ)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2) (i : Bool) :
    ‖crossLocalCutoffGradient K hK b C hgrad i‖ ≤ |C| :=
  AsymptoticL2Multiplier.operator_norm_le _ _ (abs_nonneg C) _

/-- The cross-quotient flux is first order: each summand has one energy
norm and one L2 norm. All overlap and cutoff costs remain explicit. -/
theorem crossLocalEnergyFlux_norm_le (N M : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mM)
    (b : SmoothUpperSeed) (C : ℝ)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (u : QuotientEnergySpace N) (v : QuotientEnergySpace M) :
    ‖crossLocalEnergyFlux N M K hK mN mM hmN hmM b C hgrad u v‖ ≤
      2 * Real.sqrt (mN : ℝ) * Real.sqrt (mM : ℝ) * |C| *
        (‖u‖ * ‖energyInclusion M v‖ + ‖energyInclusion N u‖ * ‖v‖) := by
  let U := quotientRestriction N K hK hK.measurableSet (energyInclusion N u)
  let V := quotientRestriction M K hK hK.measurableSet (energyInclusion M v)
  let Du := localQuotientGradient N K hK.measurableSet mN hmN
  let Dv := localQuotientGradient M K hK.measurableSet mM hmM
  let Db := crossLocalCutoffGradient K hK.measurableSet b C hgrad
  have hU : ‖U‖ ≤ Real.sqrt (mN : ℝ)*‖energyInclusion N u‖ :=
    ((quotientRestriction N K hK hK.measurableSet).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (quotientRestriction_norm_le_of_overlap N K hK mN hmN)
        (norm_nonneg _))
  have hV : ‖V‖ ≤ Real.sqrt (mM : ℝ)*‖energyInclusion M v‖ :=
    ((quotientRestriction M K hK hK.measurableSet).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (quotientRestriction_norm_le_of_overlap M K hK mM hmM)
        (norm_nonneg _))
  have hDu (i : Bool) : ‖Du i u‖ ≤ Real.sqrt (mN : ℝ)*‖u‖ :=
    ((Du i).le_opNorm u).trans (mul_le_mul_of_nonneg_right
      (localQuotientGradient_norm_le N K hK.measurableSet mN hmN i) (norm_nonneg u))
  have hDv (i : Bool) : ‖Dv i v‖ ≤ Real.sqrt (mM : ℝ)*‖v‖ :=
    ((Dv i).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (localQuotientGradient_norm_le M K hK.measurableSet mM hmM i) (norm_nonneg v))
  have hDb (i : Bool) (x : Lp ℂ 2 (volume.restrict K)) : ‖Db i x‖ ≤ |C| * ‖x‖ :=
    ((Db i).le_opNorm x).trans (mul_le_mul_of_nonneg_right
      (crossLocalCutoffGradient_norm_le K hK.measurableSet b C hgrad i) (norm_nonneg x))
  let A := Real.sqrt (mN : ℝ)*Real.sqrt (mM : ℝ)*|C| * 
    (‖u‖*‖energyInclusion M v‖+‖energyInclusion N u‖*‖v‖)
  have haxis (i : Bool) :
      ‖inner ℂ (Du i u) (Db i V) - inner ℂ (Db i U) (Dv i v)‖ ≤ A := by
    have h1 : ‖inner ℂ (Du i u) (Db i V)‖ ≤
        (Real.sqrt (mN : ℝ)*‖u‖) * (|C| * (Real.sqrt (mM : ℝ)*‖energyInclusion M v‖)) :=
      (norm_inner_le_norm _ _).trans (mul_le_mul (hDu i)
        ((hDb i V).trans (mul_le_mul_of_nonneg_left hV (abs_nonneg C)))
        (norm_nonneg _) (by positivity))
    have h2 : ‖inner ℂ (Db i U) (Dv i v)‖ ≤
        (|C| * (Real.sqrt (mN : ℝ)*‖energyInclusion N u‖)) * (Real.sqrt (mM : ℝ)*‖v‖) :=
      (norm_inner_le_norm _ _).trans (mul_le_mul
        ((hDb i U).trans (mul_le_mul_of_nonneg_left hU (abs_nonneg C)))
        (hDv i) (norm_nonneg _) (by positivity))
    apply ((norm_sub_le _ _).trans (add_le_add h1 h2)).trans_eq
    dsimp [A]
    ring
  change ‖(inner ℂ (Du true u) (Db true V) - inner ℂ (Db true U) (Dv true v)) +
    (inner ℂ (Du false u) (Db false V) - inner ℂ (Db false U) (Dv false v))‖ ≤ _
  apply ((norm_add_le _ _).trans (add_le_add (haxis true) (haxis false))).trans_eq
  dsimp [A]
  ring

#print axioms crossLocalCutoffGradient_norm_le
#print axioms crossLocalEnergyFlux_norm_le

end QuantitativeMaass
