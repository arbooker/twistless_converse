module

public import QuantitativeMaassCrossEnergyLocalizationV1
public import QuantitativeMaassCrossQuotientLocalizationV1
public import QuantitativeMaassQuotientRestrictionOverlapV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- The extension on the energy completion has the same underlying L2
vector as the literal restriction-multiplier-adjoint-restriction operator. -/
theorem crossEnergyLocalization_inclusion (N M : ℕ)
    (b : SmoothUpperSeed) (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mM)
    (B C : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (u : QuotientEnergySpace M) :
    energyInclusion N (crossEnergyLocalization N M b u) =
      crossQuotientLocalization N M K hK b hbound (energyInclusion M u) := by
  let L := (energyInclusion N).comp (crossEnergyLocalization N M b)
  let R := (crossQuotientLocalization N M K hK b hbound).comp (energyInclusion M)
  have he : L = R := by
    apply DFunLike.coe_injective
    apply (poincareEnergySeed_completion_dense M).equalizer L.continuous R.continuous
    funext v
    change energyInclusion N
        (crossEnergyLocalization N M b (poincareEnergySeed M v : QuotientEnergySpace M)) =
      crossQuotientLocalization N M K hK b hbound
        (energyInclusion M (poincareEnergySeed M v : QuotientEnergySpace M))
    rw [crossEnergyLocalization_on_seed N M b K hK hbK mN mM hmN hmM
      B C hB hbound hgrad]
    simp only [energyInclusion_coe, poincareEnergySeed_value]
    exact (crossQuotientLocalization_on_seed N M K hK b hbound hbK v).symm
  exact congrArg (fun T : QuotientEnergySpace M →L[ℂ] AutomorphicSpace N => T u) he

/-- The literal L2 transfer has the product of the two square-root
restriction multiplicities and the local multiplier bound. -/
theorem crossQuotientLocalization_norm_le_of_overlap (N M : ℕ)
    (K : Set ℍ) (hK : IsCompact K) (b : SmoothUpperSeed)
    (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mM)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B) :
    ‖crossQuotientLocalization N M K hK b hbound‖ ≤
      Real.sqrt (mN : ℝ) * B * Real.sqrt (mM : ℝ) := by
  let RN := quotientRestriction N K hK hK.measurableSet
  let RM := quotientRestriction M K hK hK.measurableSet
  have hb : ∀ᵐ z ∂volume.restrict K, ‖upperFunction b.toFun z‖ ≤ B := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact hbound z hz
  let A : Lp ℂ 2 (volume.restrict K) →L[ℂ] Lp ℂ 2 (volume.restrict K) :=
    AsymptoticL2Multiplier.operator (upperFunction b.toFun)
      (upperFunction_continuous b.smooth).aestronglyMeasurable hb
  have hA : ‖A‖ ≤ B := AsymptoticL2Multiplier.operator_norm_le
    (upperFunction b.toFun) (upperFunction_continuous b.smooth).aestronglyMeasurable hB hb
  have hRN : ‖RN.adjoint‖ ≤ Real.sqrt (mN : ℝ) := by
    rw [adjoint.norm_map]
    exact quotientRestriction_norm_le_of_overlap N K hK mN hmN
  have hRM : ‖RM‖ ≤ Real.sqrt (mM : ℝ) :=
    quotientRestriction_norm_le_of_overlap M K hK mM hmM
  change ‖RN.adjoint.comp (A.comp RM)‖ ≤ _
  calc
    _ ≤ ‖RN.adjoint‖ * ‖A.comp RM‖ := opNorm_comp_le _ _
    _ ≤ Real.sqrt (mN : ℝ) * (B * Real.sqrt (mM : ℝ)) := by
      apply mul_le_mul hRN _ (norm_nonneg (A.comp RM)) (Real.sqrt_nonneg (mN : ℝ))
      exact (opNorm_comp_le A RM).trans
        (mul_le_mul hA hRM (norm_nonneg RM) hB)
    _ = _ := (mul_assoc _ _ _).symm

/-- A real compact cutoff gives mutually adjoint transfers between the
two quotient Hilbert spaces. Realness is needed only on the restricted set. -/
theorem crossQuotientLocalization_adjoint (N M : ℕ)
    (K : Set ℍ) (hK : IsCompact K) (b : SmoothUpperSeed) {B : ℝ}
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hreal : ∀ z ∈ K, star (upperFunction b.toFun z) = upperFunction b.toFun z) :
    (crossQuotientLocalization N M K hK b hbound).adjoint =
      crossQuotientLocalization M N K hK b hbound := by
  let RN := quotientRestriction N K hK hK.measurableSet
  let RM := quotientRestriction M K hK hK.measurableSet
  have hb : ∀ᵐ z ∂volume.restrict K, ‖upperFunction b.toFun z‖ ≤ B := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact hbound z hz
  let A : Lp ℂ 2 (volume.restrict K) →L[ℂ] Lp ℂ 2 (volume.restrict K) :=
    AsymptoticL2Multiplier.operator (upperFunction b.toFun)
      (upperFunction_continuous b.smooth).aestronglyMeasurable hb
  have hA : A.adjoint = A := AsymptoticL2Multiplier.operator_adjoint
    (upperFunction b.toFun) (upperFunction_continuous b.smooth).aestronglyMeasurable hb
    (by filter_upwards [ae_restrict_mem hK.measurableSet] with z hz; exact hreal z hz)
  change (RN.adjoint.comp (A.comp RM)).adjoint = RM.adjoint.comp (A.comp RN)
  simp only [adjoint_comp, adjoint_adjoint, hA, comp_assoc]

#print axioms crossEnergyLocalization_inclusion
#print axioms crossQuotientLocalization_norm_le_of_overlap
#print axioms crossQuotientLocalization_adjoint

end QuantitativeMaass
