module

public import QuantitativeMaassEnergyLocalizationV1
public import QuantitativeMaassFriedrichsCoreV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Multiplication of a compact smooth seed by a smooth (possibly noncompact)
quotient multiplier retains the literal compact-support domain. -/
def SmoothUpperSeed.localized (u : SmoothUpperSeed) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2}) : SmoothUpperSeed where
  toFun Z := b Z*u.toFun Z
  smooth := hb.mul u.smooth
  compact := by
    change HasCompactSupport ((upperFunction b)*(upperFunction u.toFun))
    exact u.compact.mul_left

theorem congruencePoincareCartesian_mul_invariant (N : ℕ) (b u : Point→ℂ)
    (hb : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {Z : Point} (hZ : 0<Z.2) :
    congruencePoincareCartesian N (fun W => b W*u W) Z=
      b Z*congruencePoincareCartesian N u Z := by
  unfold congruencePoincareCartesian
  change poincareSum (G := gamma N) (fun z => upperFunction b z*upperFunction u z)
    (cartesianLift Z)=_
  rw [poincareSum_mul_invariant (upperFunction u) (upperFunction b) hb]
  unfold upperFunction
  rw [cartesianLift_positive Z hZ]
  rfl

/-- Localization energy inequality for the literal automorphic Poincaré
representatives; smoothness and invariance of the multiplier are explicit. -/
theorem poincare_localized_energy_bound (N : ℕ) (u : SmoothUpperSeed) (b : Point→ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {Z : Point} (hZ : 0<Z.2) :
    (hyperbolicEnergy (congruencePoincareCartesian N (u.localized b hb).toFun)
      (congruencePoincareCartesian N (u.localized b hb).toFun) Z).re≤
      2*‖b Z‖^2*(hyperbolicEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N u.toFun) Z).re+
      2*‖congruencePoincareCartesian N u.toFun Z‖^2*(hyperbolicEnergy b b Z).re := by
  have he : congruencePoincareCartesian N (u.localized b hb).toFun=ᶠ[𝓝 Z]
      (fun W => b W*congruencePoincareCartesian N u.toFun W) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hW
    exact congruencePoincareCartesian_mul_invariant N b u.toFun hi hW
  rw [hyperbolicEnergy_congr_left he,hyperbolicEnergy_congr_right he]
  exact hyperbolicEnergy_product_bound
    (congruencePoincareCartesian_smooth N u.smooth u.compact) hb hZ

#print axioms poincare_localized_energy_bound

end QuantitativeMaass
