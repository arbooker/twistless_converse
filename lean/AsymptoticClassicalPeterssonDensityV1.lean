module

public import AsymptoticClassicalPeterssonInnerV1
public import AsymptoticOrbitDensityIndependenceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalPetersson

open UpperHalfPlane MeasureTheory AsymptoticClassicalCusp
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticOrbitDensity
open scoped ENNReal

variable (N : ℕ) [NeZero N] (k : ℤ)

omit [NeZero N] in
theorem integrand_invariant (f g : CuspForm (level N) k) (a : gamma N) (z : ℍ) :
    petersson k f g (a.val • z) = petersson k f g z := by
  obtain ⟨A, hA, he⟩ := a.property
  rw [← he, integralLabel_action]
  exact SlashInvariantFormClass.petersson_smul (Γ := level N)
    (f := f) (f' := g) ⟨A, hA, rfl⟩

variable (σ : ℍ → ℝ≥0∞) (hσ : Measurable σ)
  (hnσ : ∀ z, ∑' a : gamma N, σ (a.val • z) = 1)

include hσ hnσ in
omit [NeZero N] in
/-- Every normalized orbit density has the same finite congruence mass. -/
theorem normalized_density_integral :
    (∫⁻ z : ℍ, σ z) = (∫⁻ z : ℍ, density N z) := by
  have he := lintegral_invariant_mul_eq (G := gamma N) volume
    (fun a => AsymptoticRationalGroup.measurePreserving a.val)
    (density N) σ (density_measurable N) hσ (density_orbit_sum N) hnσ
    (fun _ => 1) measurable_const (fun _ _ => rfl)
  simpa only [one_mul] using he.symm

include hσ hnσ in
/-- The integrated Petersson product is independent of the chosen
 normalized orbit density; the alternative measure is proved finite. -/
theorem inner_eq_integral_density (f g : CuspForm (level N) k) :
    inner ℂ f g = ∫ z, petersson k f g z ∂volume.withDensity σ := by
  let : IsFiniteMeasure (volume.withDensity σ) := by
    apply isFiniteMeasure_withDensity
    rw [normalized_density_integral N σ hσ hnσ,
      density_integral N (Nat.pos_of_ne_zero (NeZero.ne N))]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hm := petersson_continuous k f.holo'.continuous g.holo'.continuous
  have hi : Integrable (petersson k f g) (volume.withDensity σ) := by
    obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k (level N) f g
    apply memLp_one_iff_integrable.mp
    exact MemLp.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  rw [inner_eq_integral]
  exact integral_complex_invariant_eq (G := gamma N) volume
    (fun a => AsymptoticRationalGroup.measurePreserving a.val)
    (density N) σ (density_measurable N) hσ (density_orbit_sum N) hnσ
    (petersson k f g) hm.measurable (integrand_invariant N k f g)
    (integrable_petersson N k f g) hi

#print axioms integrand_invariant
#print axioms normalized_density_integral
#print axioms inner_eq_integral_density

end AsymptoticClassicalPetersson
