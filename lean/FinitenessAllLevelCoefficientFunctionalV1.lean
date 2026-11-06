module

public import FinitenessAllLevelDiskRestrictionV1
public import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCoefficientFunctional

open Complex Metric Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelDiskRestriction
open scoped Topology NNReal

variable {R : ℝ}

def coefficient (f : space R) (n : ℕ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ •
    ∮ z in C(0, R / 2), z⁻¹ ^ n • z⁻¹ • extend f.val z

theorem kernel_integrable (hR : 0 < R) (f : space R) (n : ℕ) :
    CircleIntegrable (fun z => z⁻¹ ^ n • z⁻¹ • extend f.val z) 0 (R / 2) := by
  apply ContinuousOn.circleIntegrable (by positivity)
  have hn : ∀ z ∈ sphere (0 : ℂ) (R / 2), z ≠ 0 := by
    intro z hz he
    subst z
    simp only [mem_sphere, dist_self] at hz
    linarith
  have hi : ContinuousOn (fun z : ℂ => z⁻¹) (sphere 0 (R / 2)) :=
    continuousOn_id.inv₀ hn
  exact (hi.pow n).smul (hi.smul (f.property.1.continuousOn.mono
    (sphere_subset_ball (by linarith))))

def coefficientLinear (hR : 0 < R) (n : ℕ) : space R →ₗ[ℂ] ℂ where
  toFun f := coefficient f n
  map_add' f g := by
    simp only [coefficient, Submodule.coe_add, extend_add, Pi.add_apply, smul_add]
    rw [circleIntegral.integral_add (kernel_integrable hR f n) (kernel_integrable hR g n)]
    exact smul_add _ _ _
  map_smul' c f := by
    simp only [coefficient, Submodule.coe_smul, extend_smul, Pi.smul_apply,
      smul_comm _ c, circleIntegral.integral_smul, RingHom.id_apply]

/-- Cauchy's coefficient bound in the actual Banach disk norm. -/
theorem coefficient_bound (hR : 0 < R) (f : space R) (n : ℕ) :
    ‖coefficient f n‖ ≤ (R / 2)⁻¹ ^ n * ‖f‖ := by
  have hh := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun z => z⁻¹ ^ n • z⁻¹ • extend f.val z)
    (c := 0) (R := R / 2) (C := (R / 2)⁻¹ ^ n * (R / 2)⁻¹ * ‖f‖)
    (by positivity : 0 ≤ R / 2) (by
      intro z hz
      have he : ‖z‖ = R / 2 := by simpa only [mem_sphere, dist_zero_right] using hz
      simp only [norm_smul, norm_pow, norm_inv, he]
      calc
        _ ≤ (R / 2)⁻¹ ^ n * ((R / 2)⁻¹ * ‖f‖) := by
          gcongr
          exact norm_extend_le f z
        _ = _ := by ring)
  change ‖coefficient f n‖ ≤ _ at hh
  convert hh using 1
  field_simp

def coefficientCLM (hR : 0 < R) (n : ℕ) : space R →L[ℂ] ℂ :=
  (coefficientLinear hR n).mkContinuous ((R / 2)⁻¹ ^ n) (fun f => coefficient_bound hR f n)

@[simp] theorem coefficientCLM_apply (hR : 0 < R) (n : ℕ) (f : space R) :
    coefficientCLM hR n f = coefficient f n := rfl

theorem coefficient_eq_cauchy (f : space R) (n : ℕ) :
    coefficient f n = cauchyPowerSeries (extend f.val) 0 (R / 2) n (fun _ => 1) := by
  rw [cauchyPowerSeries_apply]
  simp only [sub_zero, one_div]
  rfl

theorem has_series (hR : 0 < R) (f : space R) :
    HasFPowerSeriesAt (extend f.val) (cauchyPowerSeries (extend f.val) 0 (R / 2)) 0 := by
  let r : ℝ≥0 := ⟨R / 2, by positivity⟩
  have hr : 0 < r := by exact_mod_cast (half_pos hR)
  have hd : DifferentiableOn ℂ (extend f.val) (closedBall 0 r) :=
    f.property.1.mono (closedBall_subset_ball (by change R / 2 < R; linarith))
  exact (hd.hasFPowerSeriesOnBall hr).hasFPowerSeriesAt

/-- For actual polynomially bounded series these functionals recover the
literal coefficients, from agreement on the initial disk. -/
theorem coefficient_eq_of_series (hR : 0 < R) (f : space R) {a : ℕ → ℂ}
    (ha : FinitenessPolynomialSeries.PolynomialBound a)
    (he : ∀ z ∈ ball (0 : ℂ) R, extend f.val z = FinitenessPolynomialSeries.sum a z)
    (n : ℕ) : coefficientCLM hR n f = a n := by
  have hs := (has_series hR f).eq_formalMultilinearSeries_of_eventually
    (FinitenessPolynomialSeries.has_series ha)
    (Filter.mem_of_superset (ball_mem_nhds (0 : ℂ) hR) he)
  rw [coefficientCLM_apply, coefficient_eq_cauchy, hs]
  rw [FormalMultilinearSeries.ofScalars_apply_eq]
  simp

#print axioms coefficient_bound
#print axioms has_series
#print axioms coefficient_eq_of_series

end FinitenessAllLevelCoefficientFunctional
