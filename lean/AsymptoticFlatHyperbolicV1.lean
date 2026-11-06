module

public import AsymptoticStripCoordinatesV1
public import AsymptoticHyperbolicSlashV1
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFlatHyperbolic

open MeasureTheory UpperHalfPlane Filter
open AsymptoticStripCoordinates
open scoped NNReal ENNReal

noncomputable def density (z : ℍ) : ℝ≥0 := (1/NNReal.mk z.im z.im_pos.le:ℝ≥0)^2

theorem density_measurable : Measurable density := by
  unfold density
  fun_prop

theorem hyperbolic_density : (volume : Measure ℍ)=flat.withDensity (fun z => (density z:ℝ≥0∞)) := rfl

theorem hyperbolic_ac_flat : (volume : Measure ℍ)≪flat :=
  withDensity_absolutelyContinuous _ _

theorem density_cancel (z : ℍ) (u : ℂ) :
    (density z:ℝ)*‖(z.im:ℂ)*u‖^2=‖u‖^2 := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos z.im_pos]
  change (1/z.im)^2*(z.im*‖u‖)^2=‖u‖^2
  field_simp

noncomputable abbrev FlatSpace := Lp ℂ 2 flat

theorem height_memLp (f : FlatSpace) : MemLp (fun z : ℍ => (z.im:ℂ)*f z) 2 volume := by
  have hm : AEStronglyMeasurable (fun z : ℍ => (z.im:ℂ)*f z) volume :=
    (Complex.continuous_ofReal.comp continuous_im).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable f).mono_ac hyperbolic_ac_flat)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  rw [hyperbolic_density,integrable_withDensity_iff_integrable_coe_smul density_measurable]
  simpa only [smul_eq_mul,density_cancel] using
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

noncomputable def heightMapLinear : FlatSpace →ₗ[ℂ] AsymptoticHyperbolicSlash.Space where
  toFun f := (height_memLp f).toLp (fun z : ℍ => (z.im:ℂ)*f z)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (height_memLp (f+g)),
      MemLp.coeFn_toLp (height_memLp f),MemLp.coeFn_toLp (height_memLp g),
      hyperbolic_ac_flat.ae_eq (Lp.coeFn_add f g),
      Lp.coeFn_add ((height_memLp f).toLp _) ((height_memLp g).toLp _)] with z hfg hf hg ha hb
    rw [hfg,hb]
    change (z.im:ℂ)*(f+g) z=(height_memLp f).toLp _ z+(height_memLp g).toLp _ z
    rw [hf,hg,ha]
    change (z.im:ℂ)*(f z+g z)=(z.im:ℂ)*f z+(z.im:ℂ)*g z
    ring
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (height_memLp (c • f)),
      MemLp.coeFn_toLp (height_memLp f),hyperbolic_ac_flat.ae_eq (Lp.coeFn_smul c f),
      Lp.coeFn_smul c ((height_memLp f).toLp _)] with z hcf hf ha hb
    rw [hcf,hb]
    change (z.im:ℂ)*(c • f) z=c*(height_memLp f).toLp _ z
    rw [hf,ha]
    change (z.im:ℂ)*(c*f z)=c*((z.im:ℂ)*f z)
    ring

theorem heightMapLinear_coeFn (f : FlatSpace) :
    heightMapLinear f =ᵐ[volume] (fun z : ℍ => (z.im:ℂ)*f z) := MemLp.coeFn_toLp (height_memLp f)

theorem heightMapLinear_norm (f : FlatSpace) : ‖heightMapLinear f‖=‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral,AsymptoticL2Multiplier.norm_sq_eq_integral]
  calc
    (∫ z : ℍ,‖heightMapLinear f z‖^2 ∂volume)=∫ z : ℍ,‖(z.im:ℂ)*f z‖^2 ∂volume := by
      apply integral_congr_ae
      exact (heightMapLinear_coeFn f).mono (fun _ hz => congrArg (fun u : ℂ => ‖u‖^2) hz)
    _ = ∫ z : ℍ,‖f z‖^2 ∂flat := by
      rw [hyperbolic_density,integral_withDensity_eq_integral_smul density_measurable]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => density_cancel z (f z))

/-- Multiplication by y is an isometry from flat area to hyperbolic area. -/
noncomputable def heightMap : FlatSpace →ₗᵢ[ℂ] AsymptoticHyperbolicSlash.Space :=
  { heightMapLinear with norm_map' := heightMapLinear_norm }

theorem heightMap_coeFn (f : FlatSpace) :
    heightMap f =ᵐ[volume] (fun z : ℍ => (z.im:ℂ)*f z) := heightMapLinear_coeFn f

#print axioms height_memLp
#print axioms heightMapLinear_norm
#print axioms heightMap_coeFn

end AsymptoticFlatHyperbolic
