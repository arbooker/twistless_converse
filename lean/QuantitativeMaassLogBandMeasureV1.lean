module

public import QuantitativeMaassHeightBandMeasureV1
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- The exact logarithmic-height density on a compact band. -/
def logBandMeasure (w A B : ℝ) : Measure ℝ :=
  (volume.restrict (Icc A B)).withDensity (fun x => ENNReal.ofReal (w*Real.exp (-x)))

theorem logBand_density_measurable (w : ℝ) :
    Measurable (fun x : ℝ => ENNReal.ofReal (w*Real.exp (-x))) := by fun_prop

theorem logBandMeasure_finite (w A B : ℝ) : IsFiniteMeasure (logBandMeasure w A B) := by
  have hc : Continuous (fun x : ℝ => w*Real.exp (-x)) := by fun_prop
  have hi : IntegrableOn (fun x : ℝ => w*Real.exp (-x)) (Icc A B) volume :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  exact isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral

theorem logBandMeasure_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w A B : ℝ) (hw : 0≤w) (g : ℝ → E) :
    (∫ x, g x ∂logBandMeasure w A B)=∫ x in Icc A B, (w*Real.exp (-x)) • g x := by
  rw [logBandMeasure,integral_withDensity_eq_integral_toReal_smul
    (logBand_density_measurable w) (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (mul_nonneg hw (Real.exp_pos _).le)]

/-- Exact logarithmic substitution in the hyperbolic height measure. -/
theorem heightBandMeasure_integral_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w A B : ℝ) (hw : 0≤w) (g : ℝ → E) :
    (∫ y, g y ∂heightBandMeasure w (Real.exp A) (Real.exp B))=
      ∫ x in Icc A B, (w*Real.exp (-x)) • g (Real.exp x) := by
  rw [heightBandMeasure_integral w _ _ hw,← Real.image_exp_Icc]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  apply integral_congr_ae
  filter_upwards with x
  rw [abs_of_pos (Real.exp_pos x),smul_smul]
  congr 1
  rw [Real.exp_neg]
  field_simp

theorem map_exp_logBandMeasure (w A B : ℝ) (hw : 0≤w) :
    (logBandMeasure w A B).map Real.exp=heightBandMeasure w (Real.exp A) (Real.exp B) := by
  let : IsFiniteMeasure (logBandMeasure w A B) := logBandMeasure_finite w A B
  let : IsFiniteMeasure (heightBandMeasure w (Real.exp A) (Real.exp B)) :=
    heightBandMeasure_finite _ _ _ (Real.exp_pos A)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  rw [integral_map Real.continuous_exp.measurable.aemeasurable g.continuous.aestronglyMeasurable,
    logBandMeasure_integral w A B hw,heightBandMeasure_integral_exp w A B hw]

/-- Actual measure-preserving exponential chart, with both measures
constructed from hyperbolic volume rather than supplied as hypotheses. -/
theorem exp_logBand_preserving (w A B : ℝ) (hw : 0≤w) :
    MeasurePreserving Real.exp (logBandMeasure w A B)
      (heightMeasure (upperRectangle 0 w (Real.exp A) (Real.exp B))) := by
  refine ⟨Real.continuous_exp.measurable,?_⟩
  rw [map_exp_logBandMeasure w A B hw,
    heightMeasure_rectangle_eq w _ _ hw (Real.exp_pos A)]

/-- On a compact log band, the positive density dominates Lebesgue measure.
This supplies a genuine bounded local L2 change of measure. -/
theorem volume_le_logBandMeasure (w A B : ℝ) (hw : 0<w) :
    volume.restrict (Icc A B)≤
      ENNReal.ofReal ((w*Real.exp (-B))⁻¹) • logBandMeasure w A B := by
  have hm : 0<w*Real.exp (-B) := mul_pos hw (Real.exp_pos _)
  have he : (fun _ : ℝ => (1:ℝ≥0∞))≤ᵐ[volume.restrict (Icc A B)]
      fun x => ENNReal.ofReal ((w*Real.exp (-B))⁻¹)*ENNReal.ofReal (w*Real.exp (-x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hd : w*Real.exp (-B)≤w*Real.exp (-x) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hx.2)) hw.le
    have hc := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hm.le)
    rw [inv_mul_cancel₀ hm.ne'] at hc
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hm.le),← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hc
  have hh := withDensity_mono he
  rw [withDensity_const,one_smul] at hh
  rw [logBandMeasure,← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  exact hh

#print axioms heightBandMeasure_integral_exp
#print axioms exp_logBand_preserving
#print axioms volume_le_logBandMeasure

end QuantitativeMaass
