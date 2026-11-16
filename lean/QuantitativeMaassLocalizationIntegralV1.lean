module

public import QuantitativeMaassPoincareLocalizationV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass
open MaassDifferential

/-- The actual smooth form-core norm is the integral of the literal
hyperbolic mass plus gradient-energy density. -/
def poincareEnergyDensity (N : ℕ) (u : SmoothUpperSeed) (z : ℍ) : ℝ :=
  ‖poincareSum (G := gamma N) (upperFunction u.toFun) z‖^2+
    (upperEnergy (congruencePoincareCartesian N u.toFun)
      (congruencePoincareCartesian N u.toFun) z).re

theorem poincareEnergyDensity_integrable (N : ℕ) (u : SmoothUpperSeed) :
    Integrable (poincareEnergyDensity N u) (quotientMeasure N) := by
  have hm := (poincareSeed_representative N u).2.2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have he := (poincare_green_energy N u.smooth u.smooth u.compact u.compact).1.re
  exact hm.add he

theorem poincareEnergyDensity_nonnegative (N : ℕ) (u : SmoothUpperSeed) (z : ℍ) :
    0≤poincareEnergyDensity N u z :=
  add_nonneg (sq_nonneg _) (hyperbolicEnergy_self_nonneg _ _)

theorem poincareSeedVector_norm_sq_integral (N : ℕ) (u : SmoothUpperSeed) :
    ‖poincareSeedVector N u‖^2=
      ∫ z, ‖poincareSum (G := gamma N) (upperFunction u.toFun) z‖^2 ∂quotientMeasure N := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (poincareSeedVector N u)
  rw [poincareSeedVector_inner] at h
  simp only [Complex.star_def,Complex.conj_mul',← Complex.ofReal_pow,RCLike.re_to_complex] at h
  have hi : (∫ z, ((‖poincareSum (G := gamma N) (upperFunction u.toFun) z‖^2:ℝ):ℂ)
      ∂quotientMeasure N)=
      ((∫ z, ‖poincareSum (G := gamma N) (upperFunction u.toFun) z‖^2
        ∂quotientMeasure N : ℝ):ℂ) := by
    simpa only [RCLike.ofReal_eq_complex_ofReal] using
      (integral_ofReal (𝕜 := ℂ) (μ := quotientMeasure N)
        (f := fun z => ‖poincareSum (G := gamma N) (upperFunction u.toFun) z‖^2))
  rw [hi,Complex.ofReal_re] at h
  exact h.symm

theorem poincareEnergySeed_norm_sq_integral (N : ℕ) (u : SmoothUpperSeed) :
    ‖poincareEnergySeed N u‖^2=∫ z, poincareEnergyDensity N u z ∂quotientMeasure N := by
  rw [quotientEnergy_norm_sq,poincareEnergySeed_value,poincareEnergySeed_laplacian,
    poincareSeedVector_norm_sq_integral,poincareSeedVector_inner]
  have hg := poincare_green_energy N u.smooth u.smooth u.compact u.compact
  rw [upperLaplacian_congruencePoincareCartesian N u.smooth u.compact] at hg
  have hrep : upperFunction u.laplacian.toFun=upperLaplacian u.toFun := rfl
  rw [hrep,hg.2]
  have hre := integral_re hg.1
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  exact (integral_add
    ((poincareSeed_representative N u).2.2.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    hg.1.re).symm

/-- Quantitative pointwise form localization, with the actual hyperbolic
 gradient bound separated from the multiplier bound. -/
theorem poincareEnergyDensity_localized_le (N : ℕ) (u : SmoothUpperSeed) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B C : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hgrad : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) (z : ℍ) :
    poincareEnergyDensity N (u.localized b hb) z≤
      (2*B^2+2*C^2)*poincareEnergyDensity N u z := by
  have hp := poincareSum_mul_invariant (G := gamma N)
    (upperFunction u.toFun) (upperFunction b) hi z
  have he := poincare_localized_energy_bound N u b hb hi (Z := (z.re,z.im)) z.im_pos
  have hbs : ‖b (z.re,z.im)‖^2≤B^2 :=
    (sq_le_sq₀ (norm_nonneg _) hB).mpr (hbound z)
  have hg := hgrad z
  change (hyperbolicEnergy b b (z.re,z.im)).re≤C^2 at hg
  have hE := hyperbolicEnergy_self_nonneg (congruencePoincareCartesian N u.toFun) (z.re,z.im)
  have hm := sq_nonneg ‖poincareSum (G := gamma N) (upperFunction u.toFun) z‖
  have hreplace := mul_le_mul_of_nonneg_right hbs hE
  have hreplace' := mul_le_mul_of_nonneg_left hg hm
  have hmass := mul_le_mul_of_nonneg_right hbs hm
  unfold poincareEnergyDensity
  change poincareSum (G := gamma N) (fun y => upperFunction b y*upperFunction u.toFun y) z=
    upperFunction b z*poincareSum (G := gamma N) (upperFunction u.toFun) z at hp
  have hp' : poincareSum (G := gamma N) (upperFunction (u.localized b hb).toFun) z=
      b (z.re,z.im)*poincareSum (G := gamma N) (upperFunction u.toFun) z := hp
  rw [hp',norm_mul,mul_pow]
  change _+ (hyperbolicEnergy _ _ (z.re,z.im)).re≤_
  have hrep : congruencePoincareCartesian N u.toFun (z.re,z.im)=
      poincareSum (G := gamma N) (upperFunction u.toFun) z :=
    congruencePoincareCartesian_represents N u.toFun z
  rw [hrep] at he
  dsimp only [upperEnergy,upperFunction]
  nlinarith [mul_nonneg (sq_nonneg B) hm,mul_nonneg (sq_nonneg C) hE]

/-- The actual smooth Poincaré energy norm obeys the localization bound.
Together with the proved form-core density this is the quantitative input
for extending bounded smooth localization to the completed form domain. -/
theorem poincareEnergySeed_localized_norm_sq_le (N : ℕ) (u : SmoothUpperSeed) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B C : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hgrad : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) :
    ‖poincareEnergySeed N (u.localized b hb)‖^2≤
      (2*B^2+2*C^2)*‖poincareEnergySeed N u‖^2 := by
  rw [poincareEnergySeed_norm_sq_integral,poincareEnergySeed_norm_sq_integral,
    ← integral_const_mul]
  exact integral_mono (poincareEnergyDensity_integrable N _)
    ((poincareEnergyDensity_integrable N u).const_mul _)
    (poincareEnergyDensity_localized_le N u b hb hi hB hbound hgrad)

#print axioms poincareEnergySeed_norm_sq_integral
#print axioms poincareEnergySeed_localized_norm_sq_le

end QuantitativeMaass
