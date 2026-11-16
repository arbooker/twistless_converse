module

public import QuantitativeMaassQuotientWeightFluxV1
public import QuantitativeMaassEigenCutoffFluxV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson
open scoped InnerProductSpace

namespace QuantitativeMaass
open QuantitativeArithmeticMaassGradient

/-- Exact off-diagonal coefficient identity for the literal orbit-weight Gram
multiplier, with both actual quotient gradient columns. -/
theorem eigen_quotientWeight_flux (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (r μ : ℝ) (f g : AutomorphicSpace N)
    (hf : FriedrichsGraph N f ((r:ℂ) • f))
    (hg : FriedrichsGraph N g ((μ:ℂ) • g)) :
    ((r-μ:ℝ):ℂ)*inner ℂ f.val (quotientWeightMultiplier N hε hv g.val)=
      (inner ℂ (quotientGradient N true (eigenEnergyLift N r f))
          (quotientWeightGradientMultiplier N hε hv true g.val)-
        inner ℂ (quotientWeightGradientMultiplier N hε hv true f.val)
          (quotientGradient N true (eigenEnergyLift N μ g)))+
      (inner ℂ (quotientGradient N false (eigenEnergyLift N r f))
          (quotientWeightGradientMultiplier N hε hv false g.val)-
        inner ℂ (quotientWeightGradientMultiplier N hε hv false f.val)
          (quotientGradient N false (eigenEnergyLift N μ g))) := by
  have hh := quotientClosedEnergy_weight_flux N hε hv (eigenEnergyLift N r f) (eigenEnergyLift N μ g)
  rw [eigenEnergyLift_form_left N r f hf,eigenEnergyLift_form N μ g hg,
    eigenEnergyLift_inclusion N r f hf,eigenEnergyLift_inclusion N μ g hg] at hh
  have hloc (ν : ℝ) (a : AutomorphicSpace N)
      (ha : FriedrichsGraph N a ((ν:ℂ) • a)) :
      (energyInclusion N (quotientWeightEnergyMultiplier N hε hv (eigenEnergyLift N ν a))).val=
        quotientWeightMultiplier N hε hv a.val := by
    rw [quotientWeightEnergyMultiplier_value,eigenEnergyLift_inclusion N ν a ha]
  have hsym (a d : Lp ℂ 2 (quotientMeasure N)) :
      inner ℂ (quotientWeightMultiplier N hε hv a) d=
        inner ℂ a (quotientWeightMultiplier N hε hv d) := by
    simpa only [quotientWeightMultiplier_adjoint] using
      (quotientWeightMultiplier N hε hv).adjoint_inner_left d a
  change (r:ℂ)*inner ℂ f.val
      (energyInclusion N (quotientWeightEnergyMultiplier N hε hv (eigenEnergyLift N μ g))).val-
    (μ:ℂ)*inner ℂ (energyInclusion N (quotientWeightEnergyMultiplier N hε hv (eigenEnergyLift N r f))).val
      g.val=_ at hh
  rw [hloc μ g hg,hloc r f hf,hsym] at hh
  convert hh using 1
  push_cast
  ring

#print axioms eigen_quotientWeight_flux

end QuantitativeMaass
