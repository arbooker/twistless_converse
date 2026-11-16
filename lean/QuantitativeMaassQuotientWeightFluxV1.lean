module

public import QuantitativeMaassWeightedEnergyProductV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson
open scoped InnerProductSpace

namespace QuantitativeMaass
open QuantitativeArithmeticMaassGradient

/-- The literal orbit weight has the exact first-order form commutator on the
constructed energy domain; no smoothness of the weight is assumed. -/
theorem quotientClosedEnergy_weight_flux (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (u w : QuotientEnergySpace N) :
    quotientClosedEnergy N u (quotientWeightEnergyMultiplier N hε hv w)-
      quotientClosedEnergy N (quotientWeightEnergyMultiplier N hε hv u) w=
      (inner ℂ (quotientGradient N true u)
          (quotientWeightGradientMultiplier N hε hv true (energyInclusion N w).val)-
        inner ℂ (quotientWeightGradientMultiplier N hε hv true (energyInclusion N u).val)
          (quotientGradient N true w))+
      (inner ℂ (quotientGradient N false u)
          (quotientWeightGradientMultiplier N hε hv false (energyInclusion N w).val)-
        inner ℂ (quotientWeightGradientMultiplier N hε hv false (energyInclusion N u).val)
          (quotientGradient N false w)) := by
  have hs (a d : Lp ℂ 2 (quotientMeasure N)) :
      inner ℂ (quotientWeightMultiplier N hε hv a) d=
        inner ℂ a (quotientWeightMultiplier N hε hv d) := by
    simpa only [quotientWeightMultiplier_adjoint] using
      (quotientWeightMultiplier N hε hv).adjoint_inner_left d a
  rw [quotientGradient_form,quotientGradient_form,
    quotientWeightEnergyMultiplier_gradient,quotientWeightEnergyMultiplier_gradient,
    quotientWeightEnergyMultiplier_gradient,quotientWeightEnergyMultiplier_gradient]
  simp only [inner_add_left,inner_add_right,hs]
  ring

#print axioms quotientClosedEnergy_weight_flux

end QuantitativeMaass
