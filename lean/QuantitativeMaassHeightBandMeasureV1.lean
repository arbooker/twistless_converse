module

public import QuantitativeMaassHorocycleAverageV1
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- The explicit hyperbolic height measure in a width-w rectangle. -/
def heightBandMeasure (w a b : ℝ) : Measure ℝ :=
  (volume.restrict (Icc a b)).withDensity (fun y => ENNReal.ofReal (w/y^2))

theorem heightBand_density_measurable (w : ℝ) :
    Measurable (fun y : ℝ => ENNReal.ofReal (w/y^2)) := by
  fun_prop

theorem heightBandMeasure_finite (w a b : ℝ) (ha : 0<a) :
    IsFiniteMeasure (heightBandMeasure w a b) := by
  have hc : ContinuousOn (fun y : ℝ => w/y^2) (Icc a b) :=
    continuousOn_const.div (continuous_pow 2).continuousOn
      (fun y hy => pow_ne_zero 2 (ne_of_gt (ha.trans_le hy.1)))
  have hi : IntegrableOn (fun y : ℝ => w/y^2) (Icc a b) volume :=
    hc.integrableOn_compact isCompact_Icc
  exact isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral

/-- Exact integral formula, including merely measurable or nonintegrable
functions under the usual Bochner-integral convention. -/
theorem heightBandMeasure_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w a b : ℝ) (hw : 0≤w) (g : ℝ → E) :
    (∫ y, g y ∂heightBandMeasure w a b)=∫ y in Icc a b, (w/y^2) • g y := by
  rw [heightBandMeasure,integral_withDensity_eq_integral_toReal_smul
    (heightBand_density_measurable w) (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with y
  rw [ENNReal.toReal_ofReal (div_nonneg hw (sq_nonneg y))]

/-- The actual pushforward of hyperbolic volume equals the explicit height
density, proved by finite-measure determination from continuous tests. -/
theorem heightMeasure_rectangle_eq (w a b : ℝ) (hw : 0≤w) (ha : 0<a) :
    heightMeasure (upperRectangle 0 w a b)=heightBandMeasure w a b := by
  let : IsFiniteMeasure (heightMeasure (upperRectangle 0 w a b)) :=
    heightMeasure_finite _ (upperRectangle_compact 0 w a b ha)
  let : IsFiniteMeasure (heightBandMeasure w a b) := heightBandMeasure_finite w a b ha
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal,← integral_complex_ofReal]
  rw [heightMeasure_rectangle_integral 0 w a b ha (fun y => (g y:ℂ))
    (Complex.continuous_ofReal.comp g.continuous),heightBandMeasure_integral w a b hw]
  have hwidth : (volume (Icc (0:ℝ) w)).toReal=w := by
    rw [Real.volume_Icc,sub_zero,ENNReal.toReal_ofReal hw]
  simp only [hwidth,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_pow]
  apply integral_congr_ae
  filter_upwards with y
  ring

#print axioms heightBandMeasure_finite
#print axioms heightBandMeasure_integral
#print axioms heightMeasure_rectangle_eq

end QuantitativeMaass
