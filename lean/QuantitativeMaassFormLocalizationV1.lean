module

public import QuantitativeMaassLocalizationModuleV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem smoothEnergyMap_multiplier_bound (N : ℕ) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B C : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hgrad : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) (u : smoothSeedModule) :
    ‖smoothEnergyMap N (smoothSeedMultiplier b hb u)‖≤
      Real.sqrt (2*B^2+2*C^2)*‖smoothEnergyMap N u‖ := by
  change ‖(poincareEnergySeed N ((moduleSeed u).localized b hb) : QuotientEnergySpace N)‖≤
    Real.sqrt (2*B^2+2*C^2)*‖(poincareEnergySeed N (moduleSeed u) : QuotientEnergySpace N)‖
  simp only [Completion.norm_coe]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0≤2*B^2+2*C^2)]
  exact poincareEnergySeed_localized_norm_sq_le N (moduleSeed u) b hb hi hB hbound hgrad

/-- The bounded localization operator on the actual completed quotient
energy form. Its bound and action require proved smoothness, invariance and
finite bounds on the multiplier and its hyperbolic gradient. -/
def energyLocalization (N : ℕ) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2}) :
    QuotientEnergySpace N →L[ℂ] QuotientEnergySpace N :=
  ((smoothEnergyMap N).comp (smoothSeedMultiplier b hb)).extendOfNorm (smoothEnergyMap N)

theorem energyLocalization_on_seed (N : ℕ) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B C : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hgrad : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) (u : SmoothUpperSeed) :
    energyLocalization N b hb (poincareEnergySeed N u : QuotientEnergySpace N)=
      (poincareEnergySeed N (u.localized b hb) : QuotientEnergySpace N) := by
  exact LinearMap.extendOfNorm_eq (f := (smoothEnergyMap N).comp (smoothSeedMultiplier b hb))
    (e := smoothEnergyMap N) (smoothEnergyMap_dense N)
    ⟨Real.sqrt (2*B^2+2*C^2),smoothEnergyMap_multiplier_bound N b hb hi hB hbound hgrad⟩
    (seedModule u)

theorem energyLocalization_norm (N : ℕ) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B C : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hgrad : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) :
    ‖energyLocalization N b hb‖≤Real.sqrt (2*B^2+2*C^2) :=
  LinearMap.opNorm_extendOfNorm_le (f := (smoothEnergyMap N).comp (smoothSeedMultiplier b hb))
    (e := smoothEnergyMap N) (smoothEnergyMap_dense N) (Real.sqrt_nonneg _)
    (smoothEnergyMap_multiplier_bound N b hb hi hB hbound hgrad)

#print axioms energyLocalization_on_seed
#print axioms energyLocalization_norm

end QuantitativeMaass
