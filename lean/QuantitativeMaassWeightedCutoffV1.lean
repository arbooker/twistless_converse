module

public import QuantitativeMaassLocalizationFluxV1
public import QuantitativeMaassMultiplierAlgebraV1
public import QuantitativeArithmeticMaassWaveEnergyRegularityV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass.Weighted

open MaassDifferential QuantitativeArithmeticMaassGradient QuantitativeArithmeticMaassWave

/-- Explicit analytic data for a bounded smooth real invariant weight. -/
structure Cutoff (N : ℕ) where
  value : Point → ℂ
  smooth : ContDiffOn ℝ ∞ value {Z | 0<Z.2}
  invariant : ∀ g : gamma N, ∀ z : ℍ, upperFunction value (g•z)=upperFunction value z
  real : ∀ Z, star (value Z)=value Z
  bound : ℝ
  bound_nonneg : 0≤bound
  value_bound : ∀ z : ℍ, ‖upperFunction value z‖≤bound
  gradientBound : ℝ
  gradient_bound : ∀ z : ℍ, (upperEnergy value value z).re≤gradientBound^2

def multiplier (N : ℕ) (b : Cutoff N) : Lp ℂ 2 (quotientMeasure N) →L[ℂ] Lp ℂ 2 (quotientMeasure N) :=
  AsymptoticL2Multiplier.operator (upperFunction b.value)
    (upperFunction_continuous b.smooth).aestronglyMeasurable (Eventually.of_forall b.value_bound)

def gradientMultiplier (N : ℕ) (b : Cutoff N) (i : Bool) :
    Lp ℂ 2 (quotientMeasure N) →L[ℂ] Lp ℂ 2 (quotientMeasure N) :=
  cutoffGradientOperator N i b.value b.smooth b.gradient_bound

def localization (N : ℕ) (b : Cutoff N) : QuotientEnergySpace N →L[ℂ] QuotientEnergySpace N :=
  energyLocalization N b.value b.smooth

def ambientInclusion (N : ℕ) : QuotientEnergySpace N →L[ℂ] Lp ℂ 2 (quotientMeasure N) :=
  (AutomorphicSpace N).subtypeL.comp (energyInclusion N)

theorem multiplier_symmetric (N : ℕ) (b : Cutoff N) (f g : Lp ℂ 2 (quotientMeasure N)) :
    inner ℂ (multiplier N b f) g=inner ℂ f (multiplier N b g) :=
  l2Multiplier_symmetric _ _ _ (Eventually.of_forall (fun z => b.real (z.re,z.im))) f g

theorem gradientMultiplier_commute (N : ℕ) (b : Cutoff N) (i : Bool)
    (f : Lp ℂ 2 (quotientMeasure N)) :
    gradientMultiplier N b i (multiplier N b f)=multiplier N b (gradientMultiplier N b i f) := by
  have h := l2Multipliers_commute (μ := quotientMeasure N) (cutoffGradient i b.value) (upperFunction b.value)
    (cutoffGradient_continuous i b.value b.smooth).aestronglyMeasurable
    (upperFunction_continuous b.smooth).aestronglyMeasurable
    (Eventually.of_forall (cutoffGradient_norm_le i b.value b.gradient_bound))
    (Eventually.of_forall b.value_bound)
  exact congrArg (fun T : Lp ℂ 2 (quotientMeasure N) →L[ℂ] Lp ℂ 2 (quotientMeasure N) => T f) h.eq

theorem localization_ambient (N : ℕ) (b : Cutoff N) (u : QuotientEnergySpace N) :
    ambientInclusion N (localization N b u)=multiplier N b (ambientInclusion N u) := by
  have h := congrArg (fun T : AutomorphicSpace N →L[ℂ] Lp ℂ 2 (quotientMeasure N) =>
    T (energyInclusion N u))
    (quotientLocalization_ambient N b.value b.smooth b.invariant b.bound_nonneg b.value_bound b.gradient_bound)
  change (quotientLocalization N b.value b.smooth (energyInclusion N u)).val=_ at h
  rw [quotientLocalization_form N b.value b.smooth b.invariant b.bound_nonneg b.value_bound b.gradient_bound] at h
  exact h

theorem localization_gradient (N : ℕ) (b : Cutoff N) (i : Bool) (u : QuotientEnergySpace N) :
    quotientGradient N i (localization N b u)=
      multiplier N b (quotientGradient N i u)+gradientMultiplier N b i (ambientInclusion N u) :=
  quotientGradient_localized N i b.value b.smooth b.invariant b.bound_nonneg b.value_bound b.gradient_bound u

theorem localization_twice_gradient (N : ℕ) (b : Cutoff N) (i : Bool) (u : QuotientEnergySpace N) :
    quotientGradient N i (localization N b (localization N b u))=
      multiplier N b (multiplier N b (quotientGradient N i u))+
      multiplier N b (gradientMultiplier N b i (ambientInclusion N u))+
      multiplier N b (gradientMultiplier N b i (ambientInclusion N u)) := by
  rw [localization_gradient,localization_gradient,localization_ambient,map_add,gradientMultiplier_commute]

#print axioms localization_ambient
#print axioms localization_twice_gradient

end QuantitativeMaass.Weighted
