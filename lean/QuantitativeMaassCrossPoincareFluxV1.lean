module

public import QuantitativeMaassCrossPoincareEnergyV1
public import QuantitativeMaassCrossLocalizationFluxV1

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- The cross-quotient Green identity is exactly the integral of the
cutoff-gradient flux. Compactness of the cutoff supplies integrability;
there are no quotient-invariance assumptions on the cutoff. -/
theorem cross_poincare_localization_flux (N M : ℕ) (u v b : SmoothUpperSeed)
    (hr : ∀ Z, star (b.toFun Z) = b.toFun Z) :
    let F := congruencePoincareCartesian N u.toFun
    let G := congruencePoincareCartesian M v.toFun
    let bG := b.localized G (congruencePoincareCartesian_smooth M v.smooth v.compact)
    let bF := b.localized F (congruencePoincareCartesian_smooth N u.smooth u.compact)
    inner ℂ (poincareSeedVector N u.laplacian) (poincareSeedVector N bG) -
      inner ℂ (poincareSeedVector M bF) (poincareSeedVector M v.laplacian) =
    ∫ z : ℍ, (z.im : ℂ)^2 *
      ((star (X F (z.re,z.im)) * X b.toFun (z.re,z.im) * G (z.re,z.im) -
        star (X b.toFun (z.re,z.im) * F (z.re,z.im)) * X G (z.re,z.im)) +
       (star (Y F (z.re,z.im)) * Y b.toFun (z.re,z.im) * G (z.re,z.im) -
        star (Y b.toFun (z.re,z.im) * F (z.re,z.im)) * Y G (z.re,z.im))) := by
  intro F G bG bF
  have hF := congruencePoincareCartesian_smooth N u.smooth u.compact
  have hG := congruencePoincareCartesian_smooth M v.smooth v.compact
  have hi : Integrable (upperEnergy F bG.toFun) :=
    upperEnergy_integrable hF bG.smooth bG.compact
  have hj : Integrable (upperEnergy bF.toFun G) := by
    have hh := (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp
      (upperEnergy_integrable hG bF.smooth bF.compact)
    convert hh using 1
    funext z
    simp [upperEnergy, upperFunction, hyperbolicEnergy, G, mul_comm]
  rw [cross_poincare_localization_energy, ← integral_sub hi hj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  exact hyperbolicEnergy_cross_localization_flux hF hG b.smooth hr z.im_pos

#print axioms cross_poincare_localization_flux

end QuantitativeMaass
