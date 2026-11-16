module

public import QuantitativeMaassGradientLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass

open MaassDifferential QuantitativeArithmeticMaassGradient

/-- The exact gradient product rule on the completed Friedrichs form domain.
Both terms are actual bounded multipliers in ambient quotient L2. -/
theorem quotientGradient_localized (N : ℕ) (i : Bool) (b : Point → ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B C : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hg : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) (u : QuotientEnergySpace N) :
    quotientGradient N i (energyLocalization N b hb u)=
      AsymptoticL2Multiplier.operator (upperFunction b)
        (upperFunction_continuous hb).aestronglyMeasurable (Eventually.of_forall hbound)
        (quotientGradient N i u)+
      AsymptoticL2Multiplier.operator (cutoffGradient i b)
        (cutoffGradient_continuous i b hb).aestronglyMeasurable
        (Eventually.of_forall (cutoffGradient_norm_le i b hg)) (energyInclusion N u).val := by
  let M : Lp ℂ 2 (quotientMeasure N) →L[ℂ] Lp ℂ 2 (quotientMeasure N) :=
    AsymptoticL2Multiplier.operator (upperFunction b)
      (upperFunction_continuous hb).aestronglyMeasurable (Eventually.of_forall hbound)
  let D : Lp ℂ 2 (quotientMeasure N) →L[ℂ] Lp ℂ 2 (quotientMeasure N) :=
    AsymptoticL2Multiplier.operator (cutoffGradient i b)
      (cutoffGradient_continuous i b hb).aestronglyMeasurable
      (Eventually.of_forall (cutoffGradient_norm_le i b hg))
  let I := (AutomorphicSpace N).subtypeL.comp (energyInclusion N)
  let L := (quotientGradient N i).comp (energyLocalization N b hb)
  let R := M.comp (quotientGradient N i)+D.comp I
  have he : L=R := by
    apply DFunLike.coe_injective
    apply (smoothEnergyMap_dense N).equalizer L.continuous R.continuous
    funext v
    change quotientGradient N i (energyLocalization N b hb
        (poincareEnergySeed N (moduleSeed v) : QuotientEnergySpace N))=
      M (quotientGradient N i (poincareEnergySeed N (moduleSeed v) : QuotientEnergySpace N))+
      D (energyInclusion N (poincareEnergySeed N (moduleSeed v) : QuotientEnergySpace N)).val
    rw [energyLocalization_on_seed N b hb hi hB hbound hg,quotientGradient_seed,
      quotientGradient_seed,energyInclusion_coe,poincareEnergySeed_value]
    exact seedGradientLp_localized N i (moduleSeed v) b hb hi hbound hg
  exact congrArg (fun T : QuotientEnergySpace N →L[ℂ] Lp ℂ 2 (quotientMeasure N) => T u) he

#print axioms quotientGradient_localized

end QuantitativeMaass
