module

public import QuantitativeMaassPhysicalAbelSmallVariationV1
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Horizontal coordinate at unit height corresponding to signed radial distance. -/
def radialHorizontalCoordinate (r : ℝ) : ℝ := 2*Real.sinh (r/2)

theorem radialHorizontalCoordinate_hasDerivAt (r : ℝ) :
    HasDerivAt radialHorizontalCoordinate (Real.cosh (r/2)) r := by
  have hh := ((Real.hasDerivAt_sinh (r/2)).scomp r ((hasDerivAt_id r).div_const 2)).const_mul 2
  simp only [Function.comp_def,id_eq] at hh
  exact hh.congr_deriv (by ring)

theorem radialHorizontalCoordinate_cosh (r : ℝ) :
    1+(radialHorizontalCoordinate r)^2/2=Real.cosh r := by
  have hh := Real.cosh_two_mul (r/2)
  rw [show 2*(r/2)=r from by ring] at hh
  have hs := Real.cosh_sq_sub_sinh_sq (r/2)
  unfold radialHorizontalCoordinate
  nlinarith

theorem radialHorizontalCoordinate_bijective : Function.Bijective radialHorizontalCoordinate := by
  constructor
  · intro r s hrs
    have hh : Real.sinh (r/2)=Real.sinh (s/2) := by
      change 2*Real.sinh (r/2)=2*Real.sinh (s/2) at hrs
      linarith
    have he := Real.sinh_injective hh
    linarith
  · intro v
    refine ⟨2*Real.arsinh (v/2),?_⟩
    unfold radialHorizontalCoordinate
    rw [show (2*Real.arsinh (v/2))/2=Real.arsinh (v/2) from by ring,Real.sinh_arsinh]
    ring

/-- Exact equality of total horizontal and radial variation, via the genuine
hyperbolic coordinate change. No integrability premise is assumed. -/
theorem parabolicLineProfile_variation_radial (g : ℝ → ℂ)
    (hH : ContDiff ℝ ∞ (parabolicLineProfile g 1)) :
    (∫ v : ℝ,‖deriv (parabolicLineProfile g 1) v‖)=
      ∫ r : ℝ,‖deriv (fun r => g (Real.cosh r)) r‖ := by
  let H := parabolicLineProfile g 1
  have hfun : (fun r => H (radialHorizontalCoordinate r))=(fun r => g (Real.cosh r)) := by
    funext r
    simp only [H,parabolicLineProfile,one_pow,mul_one,radialHorizontalCoordinate_cosh]
  have hd (r : ℝ) : deriv (fun r => g (Real.cosh r)) r=
      Real.cosh (r/2) • deriv H (radialHorizontalCoordinate r) := by
    have hh := ((hH.differentiable (by simp)).differentiableAt.hasDerivAt).scomp r
      (radialHorizontalCoordinate_hasDerivAt r)
    simp only [Function.comp_def] at hh
    rw [hfun] at hh
    exact hh.deriv
  have him : radialHorizontalCoordinate '' univ=univ :=
    by rw [image_univ,Set.range_eq_univ.mpr radialHorizontalCoordinate_bijective.2]
  have hh := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun r (_ : r∈(univ : Set ℝ)) => (radialHorizontalCoordinate_hasDerivAt r).hasDerivWithinAt)
    radialHorizontalCoordinate_bijective.1.injOn (fun v => ‖deriv H v‖)
  simp only [him,Measure.restrict_univ] at hh
  apply hh.trans
  apply integral_congr_ae
  filter_upwards with r
  rw [hd,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.cosh_pos _),smul_eq_mul]

/-- Even radial profiles reduce total variation to one compact positive interval. -/
theorem even_compact_radial_variation (k : ℝ → ℂ) (he : Function.Even k)
    (L : ℝ) (hL : 0≤L) (hs : Function.support k⊆Icc (-L) L) :
    (∫ r : ℝ,‖deriv k r‖)=2*∫ r in (0:ℝ)..L,‖deriv k r‖ := by
  have habs (r : ℝ) : ‖deriv k |r|‖=‖deriv k r‖ := by
    rcases le_total 0 r with hr|hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_nonpos hr,even_time_deriv_odd k he,norm_neg]
  have hh := integral_comp_abs (f:=fun r => ‖deriv k r‖)
  simp_rw [habs] at hh
  rw [hh]
  congr 1
  rw [intervalIntegral.integral_of_le hL]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
  intro r hr0
  have hr : L<r := by
    by_contra hn
    exact hr0.2 ⟨hr0.1,le_of_not_gt hn⟩
  have hds := support_deriv_subset.trans (closure_minimal hs isClosed_Icc)
  have hz : deriv k r=0 := by
    by_contra hn
    exact (not_le_of_gt hr) (hds hn).2
  rw [hz,norm_zero]

#print axioms radialHorizontalCoordinate_hasDerivAt
#print axioms radialHorizontalCoordinate_cosh
#print axioms radialHorizontalCoordinate_bijective
#print axioms parabolicLineProfile_variation_radial
#print axioms even_compact_radial_variation

end QuantitativeMaass
