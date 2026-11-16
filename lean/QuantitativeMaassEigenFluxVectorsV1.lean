module

public import QuantitativeMaassEigenCutoffFluxV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson
open scoped InnerProductSpace
open QuantitativeArithmeticMaassGradient

namespace QuantitativeMaass.Weighted

def cutoffFluxEnergyVector (N : ℕ) (b : Cutoff N)
    (g : Lp ℂ 2 (quotientMeasure N)) : QuotientEnergySpace N :=
  (quotientGradient N true).adjoint (gradientMultiplier N b true g)+
    (quotientGradient N false).adjoint (gradientMultiplier N b false g)

def cutoffFluxAmbientVector (N : ℕ) (b : Cutoff N)
    (v : QuotientEnergySpace N) : Lp ℂ 2 (quotientMeasure N) :=
  (gradientMultiplier N b true).adjoint (quotientGradient N true v)+
    (gradientMultiplier N b false).adjoint (quotientGradient N false v)

theorem gradientMultiplier_norm_le (N : ℕ) (b : Cutoff N) (i : Bool) :
    ‖gradientMultiplier N b i‖≤|b.gradientBound| :=
  AsymptoticL2Multiplier.operator_norm_le _ _ (abs_nonneg _) _

theorem cutoffFluxEnergyVector_norm (N : ℕ) (b : Cutoff N)
    (g : Lp ℂ 2 (quotientMeasure N)) :
    ‖cutoffFluxEnergyVector N b g‖≤2*|b.gradientBound| *‖g‖ := by
  have hi (i : Bool) :
      ‖(quotientGradient N i).adjoint (gradientMultiplier N b i g)‖≤|b.gradientBound| *‖g‖ := by
    have h₁ := (quotientGradient N i).adjoint.le_opNorm (gradientMultiplier N b i g)
    rw [ContinuousLinearMap.adjoint.norm_map] at h₁
    have h₂ := (gradientMultiplier N b i).le_opNorm g
    have h₃ := quotientGradient_norm_le N i
    have h₄ := gradientMultiplier_norm_le N b i
    have h₅ := mul_le_mul_of_nonneg_right h₃ (norm_nonneg (gradientMultiplier N b i g))
    have h₆ := mul_le_mul_of_nonneg_right h₄ (norm_nonneg g)
    linarith
  exact (norm_add_le _ _).trans (by have h₁ := hi true; have h₂ := hi false; linarith)

theorem cutoffFluxAmbientVector_norm (N : ℕ) (b : Cutoff N)
    (v : QuotientEnergySpace N) :
    ‖cutoffFluxAmbientVector N b v‖≤2*|b.gradientBound| *‖v‖ := by
  have hi (i : Bool) :
      ‖(gradientMultiplier N b i).adjoint (quotientGradient N i v)‖≤|b.gradientBound| *‖v‖ := by
    have h₁ := (gradientMultiplier N b i).adjoint.le_opNorm (quotientGradient N i v)
    rw [ContinuousLinearMap.adjoint.norm_map] at h₁
    have h₂ := (quotientGradient N i).le_opNorm v
    have h₃ := mul_le_mul_of_nonneg_right (quotientGradient_norm_le N i) (norm_nonneg v)
    have h₄ := mul_le_mul_of_nonneg_right (gradientMultiplier_norm_le N b i)
      (norm_nonneg (quotientGradient N i v))
    have h₅ : ‖quotientGradient N i v‖≤‖v‖ := by linarith
    have h₆ := mul_le_mul_of_nonneg_left h₅ (abs_nonneg b.gradientBound)
    linarith
  exact (norm_add_le _ _).trans (by have h₁ := hi true; have h₂ := hi false; linarith)

/-- The exact cutoff flux is represented by one vector in the energy
space and one in ambient L2, to which separate Bessel inequalities apply. -/
theorem eigen_cutoff_flux_vectors (N : ℕ) (b : Cutoff N) (r μ : ℝ)
    (f g : AutomorphicSpace N)
    (hf : FriedrichsGraph N f ((r:ℂ) • f))
    (hg : FriedrichsGraph N g ((μ:ℂ) • g)) :
    ((r-μ:ℝ):ℂ)*inner ℂ f.val (multiplier N b g.val)=
      inner ℂ (eigenEnergyLift N r f) (cutoffFluxEnergyVector N b g.val)-
        inner ℂ f.val (cutoffFluxAmbientVector N b (eigenEnergyLift N μ g)) := by
  rw [eigen_cutoff_flux N b r μ f g hf hg]
  simp only [cutoffFluxEnergyVector,cutoffFluxAmbientVector,inner_add_right,
    ContinuousLinearMap.adjoint_inner_right]
  ring

#print axioms gradientMultiplier_norm_le
#print axioms cutoffFluxEnergyVector_norm
#print axioms cutoffFluxAmbientVector_norm
#print axioms eigen_cutoff_flux_vectors

end QuantitativeMaass.Weighted
