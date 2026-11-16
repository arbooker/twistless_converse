module

public import QuantitativeMaassCrossEnergyFluxBoundV1

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

variable (N M : ℕ) (K : Set ℍ) (hK : IsCompact K) (mN mM : ℕ)
  (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N), (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
  (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M), (∀ g ∈ S, g • z ∈ K) → S.card ≤ mM)
  (b : SmoothUpperSeed) (C : ℝ)
  (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)

/-- The part of the cross-quotient flux represented in the target energy space. -/
def crossFluxEnergyOperator : AutomorphicSpace M →L[ℂ] QuotientEnergySpace N :=
  let D := localQuotientGradient N K hK.measurableSet mN hmN
  let A := crossLocalCutoffGradient K hK.measurableSet b C hgrad
  let R := quotientRestriction M K hK hK.measurableSet
  (D true).adjoint.comp ((A true).comp R) +
    (D false).adjoint.comp ((A false).comp R)

/-- The part of the cross-quotient flux represented in the target L2 space. -/
def crossFluxAmbientOperator : QuotientEnergySpace M →L[ℂ] AutomorphicSpace N :=
  let D := localQuotientGradient M K hK.measurableSet mM hmM
  let A := crossLocalCutoffGradient K hK.measurableSet b C hgrad
  let R := quotientRestriction N K hK hK.measurableSet
  R.adjoint.comp ((A true).adjoint.comp (D true)) +
    R.adjoint.comp ((A false).adjoint.comp (D false))

/-- Two fixed vectors represent the flux against any target vector.
This is the representation needed for Bessel bounds, with no cylinder eigenbasis. -/
theorem crossLocalEnergyFlux_vectors (u : QuotientEnergySpace N) (v : QuotientEnergySpace M) :
    crossLocalEnergyFlux N M K hK mN mM hmN hmM b C hgrad u v =
      inner ℂ u (crossFluxEnergyOperator N M K hK mN hmN b C hgrad (energyInclusion M v)) -
        inner ℂ (energyInclusion N u) (crossFluxAmbientOperator N M K hK mM hmM b C hgrad v) := by
  simp only [crossLocalEnergyFlux, crossFluxEnergyOperator, crossFluxAmbientOperator,
    add_apply, comp_apply, inner_add_right, adjoint_inner_right]
  ring

include hmM in
theorem crossFluxEnergyOperator_norm_le :
    ‖crossFluxEnergyOperator N M K hK mN hmN b C hgrad‖ ≤
      2 * Real.sqrt (mN : ℝ) * |C| * Real.sqrt (mM : ℝ) := by
  let D := localQuotientGradient N K hK.measurableSet mN hmN
  let A := crossLocalCutoffGradient K hK.measurableSet b C hgrad
  let R := quotientRestriction M K hK hK.measurableSet
  have hterm (i : Bool) : ‖(D i).adjoint.comp ((A i).comp R)‖ ≤
      Real.sqrt (mN : ℝ) * (|C| * Real.sqrt (mM : ℝ)) := by
    have hD : ‖(D i).adjoint‖ ≤ Real.sqrt (mN : ℝ) := by
      rw [adjoint.norm_map]
      exact localQuotientGradient_norm_le N K hK.measurableSet mN hmN i
    have hA : ‖A i‖ ≤ |C| := crossLocalCutoffGradient_norm_le K hK.measurableSet b C hgrad i
    have hR : ‖R‖ ≤ Real.sqrt (mM : ℝ) := quotientRestriction_norm_le_of_overlap M K hK mM hmM
    exact (opNorm_comp_le _ _).trans (mul_le_mul hD
      ((opNorm_comp_le _ _).trans (mul_le_mul hA hR (norm_nonneg R) (abs_nonneg C)))
      (norm_nonneg ((A i).comp R)) (Real.sqrt_nonneg _))
  change ‖(D true).adjoint.comp ((A true).comp R) +
    (D false).adjoint.comp ((A false).comp R)‖ ≤ _
  apply ((norm_add_le ((D true).adjoint.comp ((A true).comp R))
    ((D false).adjoint.comp ((A false).comp R))).trans
      (add_le_add (hterm true) (hterm false))).trans_eq
  ring

include hmN in
theorem crossFluxAmbientOperator_norm_le :
    ‖crossFluxAmbientOperator N M K hK mM hmM b C hgrad‖ ≤
      2 * Real.sqrt (mN : ℝ) * |C| * Real.sqrt (mM : ℝ) := by
  let D := localQuotientGradient M K hK.measurableSet mM hmM
  let A := crossLocalCutoffGradient K hK.measurableSet b C hgrad
  let R := quotientRestriction N K hK hK.measurableSet
  have hterm (i : Bool) : ‖R.adjoint.comp ((A i).adjoint.comp (D i))‖ ≤
      Real.sqrt (mN : ℝ) * (|C| * Real.sqrt (mM : ℝ)) := by
    have hR : ‖R.adjoint‖ ≤ Real.sqrt (mN : ℝ) := by
      rw [adjoint.norm_map]
      exact quotientRestriction_norm_le_of_overlap N K hK mN hmN
    have hA : ‖(A i).adjoint‖ ≤ |C| := by
      rw [adjoint.norm_map]
      exact crossLocalCutoffGradient_norm_le K hK.measurableSet b C hgrad i
    have hD : ‖D i‖ ≤ Real.sqrt (mM : ℝ) :=
      localQuotientGradient_norm_le M K hK.measurableSet mM hmM i
    exact (opNorm_comp_le _ _).trans (mul_le_mul hR
      ((opNorm_comp_le _ _).trans (mul_le_mul hA hD (norm_nonneg (D i)) (abs_nonneg C)))
      (norm_nonneg ((A i).adjoint.comp (D i))) (Real.sqrt_nonneg _))
  change ‖R.adjoint.comp ((A true).adjoint.comp (D true)) +
    R.adjoint.comp ((A false).adjoint.comp (D false))‖ ≤ _
  apply ((norm_add_le (R.adjoint.comp ((A true).adjoint.comp (D true)))
    (R.adjoint.comp ((A false).adjoint.comp (D false)))).trans
      (add_le_add (hterm true) (hterm false))).trans_eq
  ring

#print axioms crossLocalEnergyFlux_vectors
#print axioms crossFluxEnergyOperator_norm_le
#print axioms crossFluxAmbientOperator_norm_le

end QuantitativeMaass
