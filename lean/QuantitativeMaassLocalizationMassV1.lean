module

public import QuantitativeMaassFormLocalizationV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem poincareSeedVector_localized_norm_le (N : ℕ) (u : SmoothUpperSeed) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B) :
    ‖poincareSeedVector N (u.localized b hb)‖≤B*‖poincareSeedVector N u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
  rw [mul_pow,poincareSeedVector_norm_sq_integral,poincareSeedVector_norm_sq_integral,
    ← integral_const_mul]
  apply integral_mono
    ((poincareSeed_representative N _).2.2.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    (((poincareSeed_representative N u).2.2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul _)
  intro z
  dsimp only
  have hp : poincareSum (G := gamma N) (upperFunction (u.localized b hb).toFun) z=
      upperFunction b z*poincareSum (G := gamma N) (upperFunction u.toFun) z :=
    poincareSum_mul_invariant (upperFunction u.toFun) (upperFunction b) hi z
  rw [hp,norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hB).mpr (hbound z)) (sq_nonneg _)

/-- The completed form localizer retains the sharper mass norm bound.
This is proved by density in the energy norm, not assumed from L² density. -/
theorem energyLocalization_mass_bound (N : ℕ) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B C : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hgrad : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) (v : QuotientEnergySpace N) :
    ‖energyInclusion N (energyLocalization N b hb v)‖≤B*‖energyInclusion N v‖ := by
  have hc : IsClosed {v : QuotientEnergySpace N |
      ‖energyInclusion N (energyLocalization N b hb v)‖≤B*‖energyInclusion N v‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  change v ∈ {v : QuotientEnergySpace N |
      ‖energyInclusion N (energyLocalization N b hb v)‖≤B*‖energyInclusion N v‖}
  rw [← hc.closure_eq]
  apply closure_mono (s := range (fun u : SmoothUpperSeed =>
    (poincareEnergySeed N u : QuotientEnergySpace N))) ?_ (poincareEnergySeed_completion_dense N v)
  rintro x ⟨u,rfl⟩
  change ‖energyInclusion N (energyLocalization N b hb (poincareEnergySeed N u))‖≤_
  rw [energyLocalization_on_seed N b hb hi hB hbound hgrad,energyInclusion_coe,
    energyInclusion_coe,poincareEnergySeed_value,poincareEnergySeed_value]
  exact poincareSeedVector_localized_norm_le N u b hb hi hB hbound

/-- The same literal multiplier as a bounded operator on quotient L².
Its compatibility with the completed form domain is proved below. -/
def quotientLocalization (N : ℕ) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2}) : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  ((energyInclusion N).comp (energyLocalization N b hb)).toLinearMap.extendOfNorm
    (energyInclusion N).toLinearMap

theorem quotientLocalization_form (N : ℕ) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B C : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hgrad : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) (v : QuotientEnergySpace N) :
    quotientLocalization N b hb (energyInclusion N v)=
      energyInclusion N (energyLocalization N b hb v) :=
  LinearMap.extendOfNorm_eq
    (f := ((energyInclusion N).comp (energyLocalization N b hb)).toLinearMap)
    (e := (energyInclusion N).toLinearMap) (energyInclusion_denseRange N)
    ⟨B,energyLocalization_mass_bound N b hb hi hB hbound hgrad⟩ v

theorem quotientLocalization_norm (N : ℕ) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B C : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hgrad : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) :
    ‖quotientLocalization N b hb‖≤B :=
  LinearMap.opNorm_extendOfNorm_le
    (f := ((energyInclusion N).comp (energyLocalization N b hb)).toLinearMap)
    (e := (energyInclusion N).toLinearMap) (energyInclusion_denseRange N) hB
    (energyLocalization_mass_bound N b hb hi hB hbound hgrad)

#print axioms energyLocalization_mass_bound
#print axioms quotientLocalization_form
#print axioms quotientLocalization_norm

end QuantitativeMaass
