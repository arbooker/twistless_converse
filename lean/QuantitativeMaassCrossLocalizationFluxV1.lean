module

public import QuantitativeMaassEnergyDifferentialV1

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Local flux for two different functions and a real cutoff. Neither
function nor cutoff is assumed invariant under a group. -/
theorem hyperbolicEnergy_cross_localization_flux {F G b : Point → ℂ}
    (hF : ContDiffOn ℝ ∞ F {Z | 0 < Z.2})
    (hG : ContDiffOn ℝ ∞ G {Z | 0 < Z.2})
    (hb : ContDiffOn ℝ ∞ b {Z | 0 < Z.2})
    (hr : ∀ Z, star (b Z) = b Z) {Z : Point} (hZ : 0 < Z.2) :
    hyperbolicEnergy F (fun W => G W * b W) Z -
      hyperbolicEnergy (fun W => F W * b W) G Z =
    (Z.2 : ℂ)^2 *
      ((star (X F Z) * X b Z * G Z - star (X b Z * F Z) * X G Z) +
       (star (Y F Z) * Y b Z * G Z - star (Y b Z * F Z) * Y G Z)) := by
  have hs : IsOpen {Z : Point | 0 < Z.2} := isOpen_lt continuous_const continuous_snd
  have hFX := dir_mul_smooth hs hF hb hZ e₁
  have hFY := dir_mul_smooth hs hF hb hZ e₂
  have hGX := dir_mul_smooth hs hG hb hZ e₁
  have hGY := dir_mul_smooth hs hG hb hZ e₂
  unfold hyperbolicEnergy X Y
  rw [hFX, hFY, hGX, hGY]
  simp only [star_add, star_mul, hr]
  ring

#print axioms hyperbolicEnergy_cross_localization_flux

end QuantitativeMaass
