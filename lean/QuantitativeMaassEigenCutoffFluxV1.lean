module

public import QuantitativeMaassEigenEnergyLiftV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace
open QuantitativeArithmeticMaassGradient

namespace QuantitativeMaass

/-- Conjugate symmetry of the actual completed Dirichlet form. -/
theorem quotientClosedEnergy_conj (N : ℕ) (u v : QuotientEnergySpace N) :
    star (quotientClosedEnergy N u v)=quotientClosedEnergy N v u := by
  unfold quotientClosedEnergy
  change (starRingEnd ℂ) (inner ℂ u v-inner ℂ (energyInclusion N u) (energyInclusion N v))=_
  rw [map_sub]
  exact congrArg₂ (·-·) (_root_.inner_conj_symm (𝕜 := ℂ) v u)
    (_root_.inner_conj_symm (𝕜 := ℂ) (energyInclusion N v) (energyInclusion N u))

theorem eigenEnergyLift_form_left (N : ℕ) (r : ℝ) (f : AutomorphicSpace N)
    (hf : FriedrichsGraph N f ((r:ℂ) • f)) (u : QuotientEnergySpace N) :
    quotientClosedEnergy N (eigenEnergyLift N r f) u=
      (r:ℂ)*inner ℂ f (energyInclusion N u) := by
  have hh := congrArg (starRingEnd ℂ) (eigenEnergyLift_form N r f hf u)
  have hl : (starRingEnd ℂ) (quotientClosedEnergy N u (eigenEnergyLift N r f))=
      quotientClosedEnergy N (eigenEnergyLift N r f) u := quotientClosedEnergy_conj N u _
  have hc : (starRingEnd ℂ) (r:ℂ)=(r:ℂ) := Complex.conj_ofReal r
  rw [hl,map_mul,hc,_root_.inner_conj_symm (𝕜 := ℂ)] at hh
  exact hh

namespace Weighted

/-- Exact off-diagonal coefficient identity for multiplication by a smooth
invariant real cutoff. The multiplier is not assumed to preserve cusp space
or a spectral band. -/
theorem eigen_cutoff_flux (N : ℕ) (b : Cutoff N) (r μ : ℝ)
    (f g : AutomorphicSpace N)
    (hf : FriedrichsGraph N f ((r:ℂ) • f))
    (hg : FriedrichsGraph N g ((μ:ℂ) • g)) :
    ((r-μ:ℝ):ℂ)*inner ℂ f.val (multiplier N b g.val)=
      (inner ℂ (quotientGradient N true (eigenEnergyLift N r f))
          (gradientMultiplier N b true g.val)-
        inner ℂ (gradientMultiplier N b true f.val)
          (quotientGradient N true (eigenEnergyLift N μ g)))+
      (inner ℂ (quotientGradient N false (eigenEnergyLift N r f))
          (gradientMultiplier N b false g.val)-
        inner ℂ (gradientMultiplier N b false f.val)
          (quotientGradient N false (eigenEnergyLift N μ g))) := by
  have hh := quotientClosedEnergy_localization_flux N b.value b.smooth b.invariant
    b.real b.bound_nonneg b.value_bound b.gradient_bound
    (eigenEnergyLift N r f) (eigenEnergyLift N μ g)
  change quotientClosedEnergy N (eigenEnergyLift N r f)
      (localization N b (eigenEnergyLift N μ g))-
    quotientClosedEnergy N (localization N b (eigenEnergyLift N r f))
      (eigenEnergyLift N μ g)=_ at hh
  rw [eigenEnergyLift_form_left N r f hf,eigenEnergyLift_form N μ g hg,
    eigenEnergyLift_inclusion N r f hf,eigenEnergyLift_inclusion N μ g hg] at hh
  have hloc (ν : ℝ) (v : AutomorphicSpace N)
      (hv : FriedrichsGraph N v ((ν:ℂ) • v)) :
      (energyInclusion N (localization N b (eigenEnergyLift N ν v))).val=
        multiplier N b v.val := by
    have h := localization_ambient N b (eigenEnergyLift N ν v)
    change (energyInclusion N (localization N b (eigenEnergyLift N ν v))).val=
      multiplier N b (energyInclusion N (eigenEnergyLift N ν v)).val at h
    simpa only [eigenEnergyLift_inclusion N ν v hv] using h
  change (r:ℂ)*inner ℂ f.val
      (energyInclusion N (localization N b (eigenEnergyLift N μ g))).val-
    (μ:ℂ)*inner ℂ (energyInclusion N (localization N b (eigenEnergyLift N r f))).val g.val=_ at hh
  rw [hloc μ g hg,hloc r f hf,multiplier_symmetric] at hh
  simp only [gradientMultiplier]
  convert hh using 1
  push_cast
  ring

#print axioms eigen_cutoff_flux

end Weighted

#print axioms quotientClosedEnergy_conj
#print axioms eigenEnergyLift_form_left

end QuantitativeMaass
