module

public import QuantitativeMaassQuotientWeightEigenFluxV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson
open scoped InnerProductSpace
open QuantitativeArithmeticMaassGradient

namespace QuantitativeMaass

def quotientWeightFluxEnergyVector (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (g : Lp ℂ 2 (quotientMeasure N)) : QuotientEnergySpace N :=
  (quotientGradient N true).adjoint (quotientWeightGradientMultiplier N hε ht true g)+
    (quotientGradient N false).adjoint (quotientWeightGradientMultiplier N hε ht false g)

def quotientWeightFluxAmbientVector (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (v : QuotientEnergySpace N) : Lp ℂ 2 (quotientMeasure N) :=
  (quotientWeightGradientMultiplier N hε ht true).adjoint (quotientGradient N true v)+
    (quotientWeightGradientMultiplier N hε ht false).adjoint (quotientGradient N false v)

theorem quotientWeightGradientMultiplier_abs_norm (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (i : Bool) :
    ‖quotientWeightGradientMultiplier N hε ht i‖≤|(4*quotientWeightBound ε*(2*t:ℝ))| :=
  (quotientWeightGradientMultiplier_norm N hε ht i).trans (le_abs_self _)

theorem quotientWeightFluxEnergyVector_norm (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (g : Lp ℂ 2 (quotientMeasure N)) :
    ‖quotientWeightFluxEnergyVector N hε ht g‖≤2*|(4*quotientWeightBound ε*(2*t:ℝ))| *‖g‖ := by
  have hi (i : Bool) :
      ‖(quotientGradient N i).adjoint (quotientWeightGradientMultiplier N hε ht i g)‖≤|(4*quotientWeightBound ε*(2*t:ℝ))| *‖g‖ := by
    have h₁ := (quotientGradient N i).adjoint.le_opNorm (quotientWeightGradientMultiplier N hε ht i g)
    rw [ContinuousLinearMap.adjoint.norm_map] at h₁
    have h₂ := (quotientWeightGradientMultiplier N hε ht i).le_opNorm g
    have h₃ := quotientGradient_norm_le N i
    have h₄ := quotientWeightGradientMultiplier_abs_norm N hε ht i
    have h₅ := mul_le_mul_of_nonneg_right h₃ (norm_nonneg (quotientWeightGradientMultiplier N hε ht i g))
    have h₆ := mul_le_mul_of_nonneg_right h₄ (norm_nonneg g)
    linarith
  exact (norm_add_le _ _).trans (by have h₁ := hi true; have h₂ := hi false; linarith)

theorem quotientWeightFluxAmbientVector_norm (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (v : QuotientEnergySpace N) :
    ‖quotientWeightFluxAmbientVector N hε ht v‖≤2*|(4*quotientWeightBound ε*(2*t:ℝ))| *‖v‖ := by
  have hi (i : Bool) :
      ‖(quotientWeightGradientMultiplier N hε ht i).adjoint (quotientGradient N i v)‖≤|(4*quotientWeightBound ε*(2*t:ℝ))| *‖v‖ := by
    have h₁ := (quotientWeightGradientMultiplier N hε ht i).adjoint.le_opNorm (quotientGradient N i v)
    rw [ContinuousLinearMap.adjoint.norm_map] at h₁
    have h₂ := (quotientGradient N i).le_opNorm v
    have h₃ := mul_le_mul_of_nonneg_right (quotientGradient_norm_le N i) (norm_nonneg v)
    have h₄ := mul_le_mul_of_nonneg_right (quotientWeightGradientMultiplier_abs_norm N hε ht i)
      (norm_nonneg (quotientGradient N i v))
    have h₅ : ‖quotientGradient N i v‖≤‖v‖ := by linarith
    have h₆ := mul_le_mul_of_nonneg_left h₅ (abs_nonneg (4*quotientWeightBound ε*(2*t:ℝ)))
    linarith
  exact (norm_add_le _ _).trans (by have h₁ := hi true; have h₂ := hi false; linarith)

/-- The exact literal orbit-weight flux is represented by one vector in the energy
space and one in ambient L2, to which separate Bessel inequalities apply. -/
theorem eigen_quotientWeight_flux_vectors (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (r μ : ℝ)
    (f g : AutomorphicSpace N)
    (hf : FriedrichsGraph N f ((r:ℂ) • f))
    (hg : FriedrichsGraph N g ((μ:ℂ) • g)) :
    ((r-μ:ℝ):ℂ)*inner ℂ f.val (quotientWeightMultiplier N hε ht g.val)=
      inner ℂ (eigenEnergyLift N r f) (quotientWeightFluxEnergyVector N hε ht g.val)-
        inner ℂ f.val (quotientWeightFluxAmbientVector N hε ht (eigenEnergyLift N μ g)) := by
  rw [eigen_quotientWeight_flux N hε ht r μ f g hf hg]
  simp only [quotientWeightFluxEnergyVector,quotientWeightFluxAmbientVector,inner_add_right,
    ContinuousLinearMap.adjoint_inner_right]
  ring

#print axioms quotientWeightGradientMultiplier_abs_norm
#print axioms quotientWeightFluxEnergyVector_norm
#print axioms quotientWeightFluxAmbientVector_norm
#print axioms eigen_quotientWeight_flux_vectors

end QuantitativeMaass
