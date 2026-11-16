module

public import QuantitativeMaassLocalizationMassV1
public import AsymptoticL2MultiplierV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem quotientLocalization_on_seed (N : ℕ) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B C : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hg : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) (u : SmoothUpperSeed) :
    quotientLocalization N b hb (poincareSeedVector N u)=
      poincareSeedVector N (u.localized b hb) := by
  have h := quotientLocalization_form N b hb hi hB hbound hg
    (poincareEnergySeed N u : QuotientEnergySpace N)
  rw [energyLocalization_on_seed N b hb hi hB hbound hg,energyInclusion_coe,
    energyInclusion_coe,poincareEnergySeed_value,poincareEnergySeed_value] at h
  exact h

/-- Identification with the literal bounded multiplier on ambient quotient
L²; the form-completion construction introduces no hidden representative. -/
theorem quotientLocalization_ambient (N : ℕ) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B C : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hg : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) :
    (AutomorphicSpace N).subtypeL.comp (quotientLocalization N b hb)=
      (AsymptoticL2Multiplier.operator (upperFunction b)
        (upperFunction_continuous hb).aestronglyMeasurable
        (Filter.Eventually.of_forall hbound)).comp (AutomorphicSpace N).subtypeL := by
  apply DFunLike.coe_injective
  apply (poincareSeedVector_dense N).equalizer (by fun_prop) (by fun_prop)
  funext u
  change (quotientLocalization N b hb (poincareSeedVector N u)).val=
    AsymptoticL2Multiplier.operator (upperFunction b)
      (upperFunction_continuous hb).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound) (poincareSeedVector N u).val
  rw [quotientLocalization_on_seed N b hb hi hB hbound hg]
  apply Lp.ext
  filter_upwards [poincareSeedVector_coeFn N (u.localized b hb),poincareSeedVector_coeFn N u,
    AsymptoticL2Multiplier.operator_coeFn (upperFunction b)
      (upperFunction_continuous hb).aestronglyMeasurable (Filter.Eventually.of_forall hbound)
      (poincareSeedVector N u).val] with z hbu hu hm
  rw [hbu,hm,hu]
  exact poincareSum_mul_invariant (upperFunction u.toFun) (upperFunction b) hi z

theorem quotientLocalization_coeFn (N : ℕ) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B C : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hg : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) (v : AutomorphicSpace N) :
    ((quotientLocalization N b hb v).val : ℍ→ℂ)=ᵐ[quotientMeasure N]
      (fun z => upperFunction b z*(v.val : ℍ→ℂ) z) := by
  have h := congrArg (fun A : AutomorphicSpace N →L[ℂ] Lp ℂ 2 (quotientMeasure N) => A v)
    (quotientLocalization_ambient N b hb hi hB hbound hg)
  change (quotientLocalization N b hb v).val=
    AsymptoticL2Multiplier.operator (upperFunction b)
      (upperFunction_continuous hb).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound) v.val at h
  rw [h]
  exact AsymptoticL2Multiplier.operator_coeFn _ _ _ _

#print axioms quotientLocalization_ambient
#print axioms quotientLocalization_coeFn

end QuantitativeMaass
