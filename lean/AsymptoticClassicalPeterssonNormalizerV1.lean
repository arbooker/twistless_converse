module

public import AsymptoticOrbitDensityNormalizerV1
public import AsymptoticClassicalPeterssonDensityV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalPetersson

open UpperHalfPlane MeasureTheory AsymptoticClassicalCusp
open AsymptoticCongruenceStrip AsymptoticOrbitDensity
open scoped ModularForm InnerProduct ENNReal

variable (N : ℕ) [NeZero N] (k : ℤ)
variable (u : AsymptoticRationalGroup.Group) (R : GL (Fin 2) ℝ)
variable (hR : 0 < R.det.val) (haction : ∀ z : ℍ, R • z = u • z)
variable (hc : ∀ a ∈ gamma N, u * a * u⁻¹ ∈ gamma N)
variable (hci : ∀ a ∈ gamma N, u⁻¹ * a * u ∈ gamma N)

include hR haction hc hci in
/-- Slash by a positive rational normalizer has its exact Petersson
 scaling factor. All four forms belong to the actual classical cusp space. -/
theorem inner_slash_normalizer (f g f' g' : CuspForm (level N) k)
    (hf' : (f' : ℍ → ℂ) = (f : ℍ → ℂ) ∣[k] R)
    (hg' : (g' : ℍ → ℂ) = (g : ℍ → ℂ) ∣[k] R) :
    inner ℂ f' g' = (R.det.val : ℂ) ^ (k - 2) * inner ℂ f g := by
  have hfin : (∫⁻ z : ℍ, density N z ∂volume) ≠ ∞ := by
    rw [density_integral N (Nat.pos_of_ne_zero (NeZero.ne N))]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k (level N) f g
  rw [inner_eq_integral N k f' g']
  change (∫ z, petersson k (f' : ℍ → ℂ) (g' : ℍ → ℂ) z
    ∂volume.withDensity (density N)) = _
  rw [hf', hg']
  simp only [petersson_slash, σ, hR, ite_true, ContinuousAlgEquiv.refl_apply,
    abs_of_pos hR, haction]
  rw [integral_const_mul]
  congr 1
  rw [integral_normalizer (gamma N) u hc hci volume AsymptoticRationalGroup.measurePreserving
    (density N) (density_measurable N) (density_orbit_sum N) hfin
    (petersson k f g) (petersson_continuous k f.holo'.continuous g.holo'.continuous).measurable
    (integrand_invariant N k f g) C hC]
  exact (inner_eq_integral N k f g).symm

#print axioms inner_slash_normalizer

end AsymptoticClassicalPetersson
