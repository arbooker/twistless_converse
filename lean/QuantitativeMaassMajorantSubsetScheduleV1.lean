module

public import QuantitativeMaassEnlargedSubsetScheduleV1
public import QuantitativeMaassMajorantTraceNormalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- Exact normalization of the energy on any spatial subset. -/
theorem originalMajorant_subset_energy_eq (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (ε : ℝ→ℝ) (t : ℝ) (S : Set ℍ) :
    (∫ z in S,‖originalMajorantColumn K hc he ε t z‖^2) =
      (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹^2 *
        ∫ z in S,‖enlargedWindowColumn K hc he ε t z‖^2 := by
  have heq (z : ℍ) : ‖originalMajorantColumn K hc he ε t z‖^2 =
      (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹^2 *
        ‖enlargedWindowColumn K hc he ε t z‖^2 := by
    rw [originalMajorantColumn_eq_smul,norm_smul,mul_pow,norm_inv,
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (QuantitativeNinaMaass.windowEnergyDenominator_pos K ε t)]
    rfl
  simp_rw [heq]
  exact integral_const_mul _ _

/-- Negligible area implies negligible energy for the literal normalized packet. -/
theorem originalMajorant_subset_energy_weighted_limit (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (S : ℝ→Set ℍ) (H W : ℝ) (hH : 0≤H)
    (hsize : ∀ᶠ t in atTop,S t⊆Metric.closedBall I (H*Strong.strongScale t))
    (harea : Tendsto (fun t => Real.exp (W*Strong.strongScale t)*volume.real (S t)) atTop (𝓝 0)) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (∫ z in S t,‖originalMajorantColumn K hc he ε t z‖^2)/(t*ε t)) atTop (𝓝 0) := by
  have hlim := (originalMajorant_normalization_sq_limit K ε
    (hε.mono (fun _ h => h.1)) hp).mul
    (enlarged_subset_energy_weighted_limit K hc he hK hm ε hε hp S H W hH hsize harea)
  rw [mul_zero] at hlim
  convert hlim using 1
  funext t
  rw [originalMajorant_subset_energy_eq]
  ring

#print axioms originalMajorant_subset_energy_eq
#print axioms originalMajorant_subset_energy_weighted_limit
end QuantitativeMaass.Scheduled
