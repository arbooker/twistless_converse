module

public import QuantitativeMaassWeightedCutoffV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Weighted

open QuantitativeArithmeticMaassGradient QuantitativeArithmeticMaassWave

/-- Weighted Green identity with the actual Friedrichs operator. The two
cutoff-gradient terms are the exact flux left after kinetic/gradient cancellation. -/
theorem weighted_green (N : ℕ) (b : Cutoff N) {x y : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) (v : QuotientEnergySpace N) :
    inner ℂ (multiplier N b (ambientInclusion N v)) (multiplier N b y.val)=
      inner ℂ (multiplier N b (quotientGradient N true v))
        (multiplier N b (quotientGradient N true (graphEnergyLift N x y)))+
      inner ℂ (multiplier N b (quotientGradient N false v))
        (multiplier N b (quotientGradient N false (graphEnergyLift N x y)))+
      2*(inner ℂ (gradientMultiplier N b true (ambientInclusion N v))
          (multiplier N b (quotientGradient N true (graphEnergyLift N x y)))+
        inner ℂ (gradientMultiplier N b false (ambientInclusion N v))
          (multiplier N b (quotientGradient N false (graphEnergyLift N x y)))) := by
  have hform : quotientClosedEnergy N (localization N b (localization N b v))
      (graphEnergyLift N x y)=
      inner ℂ (ambientInclusion N (localization N b (localization N b v))) y.val :=
    graphEnergyLift_form N hxy _
  rw [localization_ambient,localization_ambient] at hform
  calc
    _ = inner ℂ (multiplier N b (multiplier N b (ambientInclusion N v))) y.val :=
      (multiplier_symmetric N b (multiplier N b (ambientInclusion N v)) y.val).symm
    _ = quotientClosedEnergy N (localization N b (localization N b v))
        (graphEnergyLift N x y) := hform.symm
    _ = _ := by
      rw [quotientGradient_form,localization_twice_gradient,localization_twice_gradient]
      simp only [inner_add_left,multiplier_symmetric]
      ring

#print axioms weighted_green

end QuantitativeMaass.Weighted
