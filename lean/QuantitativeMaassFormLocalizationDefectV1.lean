module

public import QuantitativeMaassEnergyLocalizationIdentityV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem poincareClosedEnergy_integral (N : ℕ) (u v : SmoothUpperSeed) :
    quotientClosedEnergy N (poincareEnergySeed N u) (poincareEnergySeed N v)=
      ∫ z, upperEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N v.toFun) z ∂quotientMeasure N := by
  rw [quotientClosedEnergy_coe,poincareEnergySeed_value,poincareEnergySeed_laplacian,
    poincareSeedVector_inner]
  have h := poincare_green_energy N u.smooth v.smooth u.compact v.compact
  rw [upperLaplacian_congruencePoincareCartesian N v.smooth v.compact] at h
  exact h.2

theorem poincareClosedEnergy_re_integral (N : ℕ) (u v : SmoothUpperSeed) :
    (quotientClosedEnergy N (poincareEnergySeed N u) (poincareEnergySeed N v)).re=
      ∫ z, (upperEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N v.toFun) z).re ∂quotientMeasure N := by
  rw [poincareClosedEnergy_integral]
  have h := integral_re (poincare_green_energy N u.smooth v.smooth u.compact v.compact).1
  simpa only [RCLike.re_to_complex] using h.symm

theorem localized_poincare_germ (N : ℕ) (u : SmoothUpperSeed) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {Z : Point} (hZ : 0<Z.2) :
    congruencePoincareCartesian N (u.localized b hb).toFun=ᶠ[𝓝 Z]
      (fun W => b W*congruencePoincareCartesian N u.toFun W) := by
  filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hW
  exact congruencePoincareCartesian_mul_invariant N b u.toFun hi hW

/-- Exact localized energy identity for literal quotient Poincaré sums. -/
theorem poincare_localization_identity (N : ℕ) (u : SmoothUpperSeed) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    (hr : ∀ Z, star (b Z)=b Z) (z : ℍ) :
    (upperEnergy (congruencePoincareCartesian N (u.localized b hb).toFun)
      (congruencePoincareCartesian N (u.localized b hb).toFun) z).re=
    (upperEnergy (congruencePoincareCartesian N u.toFun)
      (congruencePoincareCartesian N ((u.localized b hb).localized b hb).toFun) z).re+
    ‖poincareSum (G := gamma N) (upperFunction u.toFun) z‖^2*(upperEnergy b b z).re := by
  have h1 := localized_poincare_germ N u b hb hi (Z := (z.re,z.im)) z.im_pos
  have h2 := localized_poincare_germ N (u.localized b hb) b hb hi (Z := (z.re,z.im)) z.im_pos
  have h3 : congruencePoincareCartesian N ((u.localized b hb).localized b hb).toFun=ᶠ[𝓝 (z.re,z.im)]
      (fun W => b W*(b W*congruencePoincareCartesian N u.toFun W)) :=
    h2.trans ((Filter.EventuallyEq.refl _ _).mul h1)
  dsimp only [upperEnergy,upperFunction]
  rw [hyperbolicEnergy_congr_left h1,hyperbolicEnergy_congr_right h1,
    hyperbolicEnergy_congr_right h3]
  have h := hyperbolicEnergy_localization_identity
    (congruencePoincareCartesian_smooth N u.smooth u.compact) hb hr
    (Z := (z.re,z.im)) z.im_pos
  have hrep : congruencePoincareCartesian N u.toFun (z.re,z.im)=
    poincareSum (G := gamma N) (upperFunction u.toFun) z :=
      congruencePoincareCartesian_represents N u.toFun z
  rw [hrep] at h
  exact h

/-- The gradient error in localization is bounded on the actual smooth
form core, with no derivative of the measurable quotient density. -/
theorem poincare_localization_defect_le (N : ℕ) (u : SmoothUpperSeed) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    (hr : ∀ Z, star (b Z)=b Z) {C : ℝ}
    (hg : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) :
    (quotientClosedEnergy N (poincareEnergySeed N (u.localized b hb))
      (poincareEnergySeed N (u.localized b hb))).re≤
    (quotientClosedEnergy N (poincareEnergySeed N u)
      (poincareEnergySeed N ((u.localized b hb).localized b hb))).re+
      C^2*‖poincareSeedVector N u‖^2 := by
  rw [poincareClosedEnergy_re_integral,poincareClosedEnergy_re_integral,
    poincareSeedVector_norm_sq_integral,← integral_const_mul]
  have hE := (poincare_green_energy N u.smooth
    ((u.localized b hb).localized b hb).smooth u.compact
    ((u.localized b hb).localized b hb).compact).1.re
  simp only [RCLike.re_to_complex] at hE
  have hm := ((poincareSeed_representative N u).2.2.integrable_norm_pow
    (by norm_num : (2:ℕ)≠0)).const_mul (C^2)
  rw [← integral_add hE hm]
  have hL := (poincare_green_energy N (u.localized b hb).smooth (u.localized b hb).smooth
      (u.localized b hb).compact (u.localized b hb).compact).1.re
  simp only [RCLike.re_to_complex] at hL
  apply integral_mono hL (hE.add hm)
  intro z
  dsimp only
  rw [poincare_localization_identity N u b hb hi hr]
  dsimp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left (hg z)
    (sq_nonneg ‖poincareSum (G := gamma N) (upperFunction u.toFun) z‖)]

/-- The same gradient-error estimate on the complete, actual Friedrichs
form domain. This follows from the proved smooth form core and bounded
localizers, rather than a form-locality hypothesis. -/
theorem energyLocalization_defect_le (N : ℕ) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    (hr : ∀ Z, star (b Z)=b Z) {B C : ℝ} (hB : 0≤B)
    (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hg : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) (v : QuotientEnergySpace N) :
    (quotientClosedEnergy N (energyLocalization N b hb v) (energyLocalization N b hb v)).re≤
    (quotientClosedEnergy N v (energyLocalization N b hb (energyLocalization N b hb v))).re+
      C^2*‖energyInclusion N v‖^2 := by
  let S : Set (QuotientEnergySpace N) := {v |
    (quotientClosedEnergy N (energyLocalization N b hb v) (energyLocalization N b hb v)).re≤
    (quotientClosedEnergy N v (energyLocalization N b hb (energyLocalization N b hb v))).re+
      C^2*‖energyInclusion N v‖^2}
  have hc : IsClosed S := by
    apply isClosed_le
    all_goals unfold quotientClosedEnergy; fun_prop
  change v∈S
  rw [← hc.closure_eq]
  apply closure_mono (s := range (fun u : SmoothUpperSeed =>
    (poincareEnergySeed N u : QuotientEnergySpace N))) ?_ (poincareEnergySeed_completion_dense N v)
  rintro x ⟨u,rfl⟩
  dsimp only [S,mem_ofPred_eq]
  rw [energyLocalization_on_seed N b hb hi hB hbound hg,
    energyLocalization_on_seed N b hb hi hB hbound hg,energyInclusion_coe,poincareEnergySeed_value]
  exact poincare_localization_defect_le N u b hb hi hr hg

#print axioms poincare_localization_defect_le
#print axioms energyLocalization_defect_le

end QuantitativeMaass
