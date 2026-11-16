module

public import QuantitativeMaassCuspTensorSeedV1
public import QuantitativeMaassCuspRectangleIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem cartesianLift_horizontal_continuous (y : ℝ) (hy : 0<y) :
    Continuous (fun x : ℝ => cartesianLift (x,y)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (cartesianLift_continuousAt _ hy).comp
    (continuous_id.prodMk continuous_const).continuousAt

/-- Horizontal periodic partition identity with the actual hyperbolic
measure. The larger compact rectangle supports a smooth test. -/
theorem rectangle_periodCutoff_integral (w a b : ℝ) (hw : 0<w) (ha : 0<a)
    (F : ℍ → ℂ) (hF : Continuous F)
    (hp : ∀ y, 0<y → Function.Periodic (fun x => F (cartesianLift (x,y))) w) :
    (∫ Z in upperRectangle 0 (2*w) a b, (periodCutoff (Z.re/w):ℂ)*F Z)=
      ∫ Z in upperRectangle 0 w a b, F Z := by
  have hc : Continuous (fun Z : ℍ => (periodCutoff (Z.re/w):ℂ)*F Z) :=
    (Complex.continuous_ofReal.comp
      (periodCutoff_smooth.continuous.comp (continuous_re.div_const w))).mul hF
  rw [integral_upperRectangle_iterated 0 (2*w) a b ha _ hc,
    integral_upperRectangle_iterated 0 w a b ha F hF]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  have hpos := ha.trans_le hy.1
  have he : (fun x : ℝ => (periodCutoff ((cartesianLift (x,y)).re/w):ℂ)*
      F (cartesianLift (x,y))/(y:ℂ)^2)=
      fun x => ((periodCutoff (x/w):ℂ)*F (cartesianLift (x,y)))/(y:ℂ)^2 := by
    funext x
    rw [cartesianLift_positive _ hpos]
    rfl
  rw [he,integral_div,integral_div]
  congr 1
  exact periodCutoff_setIntegral_width w hw _
    (hF.comp (cartesianLift_horizontal_continuous y hpos)) (hp y hpos)

/-- Exact cancellation of the compact test's horizontal second derivative
in a hyperbolic rectangle, for actual periodic continuous functions. -/
theorem rectangle_periodCutoff_second_integral (w a b : ℝ) (hw : 0<w) (ha : 0<a)
    (F : ℍ → ℂ) (hF : Continuous F)
    (hp : ∀ y, 0<y → Function.Periodic (fun x => F (cartesianLift (x,y))) w) :
    (∫ Z in upperRectangle 0 (2*w) a b,
      ((deriv (deriv periodCutoff) (Z.re/w):ℝ):ℂ)*F Z)=0 := by
  have hd : ContDiff ℝ ∞ (deriv periodCutoff) := (contDiff_infty_iff_deriv.mp periodCutoff_smooth).2
  have hc : Continuous (fun Z : ℍ => ((deriv (deriv periodCutoff) (Z.re/w):ℝ):ℂ)*F Z) :=
    (Complex.continuous_ofReal.comp
      ((hd.continuous_deriv (by simp)).comp (continuous_re.div_const w))).mul hF
  rw [integral_upperRectangle_iterated 0 (2*w) a b ha _ hc]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  have hpos := ha.trans_le hy.1
  have he : (fun x : ℝ => ((deriv (deriv periodCutoff) ((cartesianLift (x,y)).re/w):ℝ):ℂ)*
      F (cartesianLift (x,y))/(y:ℂ)^2)=
      fun x => (((deriv (deriv periodCutoff) (x/w):ℝ):ℂ)*F (cartesianLift (x,y)))/(y:ℂ)^2 := by
    funext x
    rw [cartesianLift_positive _ hpos]
    rfl
  rw [he,integral_div]
  have hz : (∫ x in Icc (0:ℝ) (2*w), ((deriv (deriv periodCutoff) (x/w):ℝ):ℂ)*
      F (cartesianLift (x,y)))=0 :=
    periodCutoff_second_setIntegral_width w hw _
      (hF.comp (cartesianLift_horizontal_continuous y hpos)) (hp y hpos)
  rw [hz,zero_div]
  rfl

#print axioms rectangle_periodCutoff_integral
#print axioms rectangle_periodCutoff_second_integral

end QuantitativeMaass
