module

public import AsymptoticFlatHyperbolicV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFlatHyperbolic

open MeasureTheory UpperHalfPlane Filter
open AsymptoticStripCoordinates
open scoped NNReal ENNReal

theorem flat_ac_hyperbolic : flat≪(volume : Measure ℍ) := by
  rw [hyperbolic_density]
  apply withDensity_absolutelyContinuous' density_measurable.coe_nnreal_ennreal.aemeasurable
  apply Eventually.of_forall
  intro z
  apply ENNReal.coe_ne_zero.mpr
  change (1/NNReal.mk z.im z.im_pos.le)^2≠0
  exact pow_ne_zero _ (div_ne_zero one_ne_zero (by
    intro hz
    exact z.im_pos.ne' (congrArg (fun r : ℝ≥0 => (r:ℝ)) hz)))

theorem inverse_height_density (z : ℍ) (u : ℂ) :
    ‖(z.im:ℂ)⁻¹*u‖^2=(density z:ℝ)*‖u‖^2 := by
  simp [density,mul_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos z.im_pos]

theorem inverseHeight_memLp (u : AsymptoticHyperbolicSlash.Space) :
    MemLp (fun z : ℍ => (z.im:ℂ)⁻¹*u z) 2 flat := by
  have hm : AEStronglyMeasurable (fun z : ℍ => (z.im:ℂ)⁻¹*u z) flat :=
    (Complex.continuous_ofReal.comp continuous_im).measurable.inv.aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable u).mono_ac flat_ac_hyperbolic)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hu := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  change Integrable (fun z : ℍ => ‖u z‖^2) (flat.withDensity (fun z => (density z:ℝ≥0∞))) at hu
  rw [integrable_withDensity_iff_integrable_coe_smul density_measurable] at hu
  simpa only [inverse_height_density,smul_eq_mul] using hu

noncomputable def inverseHeight (u : AsymptoticHyperbolicSlash.Space) : FlatSpace :=
  (inverseHeight_memLp u).toLp (fun z : ℍ => (z.im:ℂ)⁻¹*u z)

theorem inverseHeight_coeFn (u : AsymptoticHyperbolicSlash.Space) :
    inverseHeight u =ᵐ[flat] (fun z : ℍ => (z.im:ℂ)⁻¹*u z) :=
  MemLp.coeFn_toLp (inverseHeight_memLp u)

theorem heightMap_inverseHeight (u : AsymptoticHyperbolicSlash.Space) : heightMap (inverseHeight u)=u := by
  apply Lp.ext
  filter_upwards [heightMap_coeFn (inverseHeight u),hyperbolic_ac_flat.ae_eq (inverseHeight_coeFn u)] with z hh hi
  rw [hh,hi,← mul_assoc,mul_inv_cancel₀ (by exact_mod_cast z.im_pos.ne'),one_mul]

#print axioms flat_ac_hyperbolic
#print axioms inverseHeight_memLp
#print axioms inverseHeight_coeFn
#print axioms heightMap_inverseHeight

end AsymptoticFlatHyperbolic
