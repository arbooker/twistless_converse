module

public import QuantitativeMaassSublevelIntegralV1
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- A nonzero complex affine slope gives a linear one-dimensional
sublevel bound in a real averaging parameter. -/
theorem complex_affine_parameter_sublevel (a b : ℂ) (m r : ℝ)
    (hm : 0<m) (ha : m≤‖a‖) (_hr : 0<r) :
    volume {u : ℝ | ‖(u:ℂ)*a+b‖<r}≤ENNReal.ofReal (4*r/m) := by
  by_cases he : ({u : ℝ | ‖(u:ℂ)*a+b‖<r} : Set ℝ).Nonempty
  · obtain ⟨u₀,hu₀⟩ := he
    change ‖(u₀:ℂ)*a+b‖<r at hu₀
    have hsub : {u : ℝ | ‖(u:ℂ)*a+b‖<r}⊆Ioo (u₀-2*r/m) (u₀+2*r/m) := by
      intro u hu
      change ‖(u:ℂ)*a+b‖<r at hu
      have hh : |u-u₀| *m<2*r := by
        calc
          _≤|u-u₀| *‖a‖ := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
          _=‖((u:ℂ)*a+b)-((u₀:ℂ)*a+b)‖ := by
            rw [show ((u:ℂ)*a+b)-((u₀:ℂ)*a+b)=((u-u₀:ℝ):ℂ)*a by push_cast;ring,
              norm_mul,Complex.norm_real,Real.norm_eq_abs]
          _≤‖(u:ℂ)*a+b‖+‖(u₀:ℂ)*a+b‖ := norm_sub_le _ _
          _<2*r := by linarith
      have hd := (lt_div_iff₀ hm).mpr hh
      have hpair := abs_lt.mp hd
      exact ⟨by linarith,by linarith⟩
    apply (measure_mono hsub).trans_eq
    rw [Real.volume_Ioo]
    congr 1
    ring
  · rw [Set.not_nonempty_iff_eq_empty.mp he,measure_empty]
    exact bot_le

/-- The reciprocal square root of an actual affine parameter displacement
is integrable on one averaging period, with an explicit slope cost. -/
theorem complex_affine_parameter_inverse_sqrt (a b : ℂ) (m : ℝ)
    (hm : 0<m) (ha : m≤‖a‖) :
    IntegrableOn (fun u : ℝ => 1/Real.sqrt ‖(u:ℂ)*a+b‖) (Icc (0:ℝ) 1) ∧
    (∫ u in Icc (0:ℝ) 1,1/Real.sqrt ‖(u:ℂ)*a+b‖)≤Real.pi*(1+4/m) := by
  apply inverse_sqrt_integrable_of_sublevel (volume.restrict (Icc (0:ℝ) 1))
    (fun u : ℝ => ‖(u:ℂ)*a+b‖) (by fun_prop) (fun _ => norm_nonneg _) 1 (4/m)
    (by norm_num) (by positivity)
  · rw [Measure.restrict_apply_univ,Real.volume_Icc]
    norm_num
  · intro r hr
    apply (Measure.restrict_apply_le _ _).trans
    convert complex_affine_parameter_sublevel a b m r hm ha hr using 1
    congr 1
    ring

/-- The isolated identity parameter in an averaging word has zero measure. -/
theorem complex_affine_parameter_zero_null (a b : ℂ) (ha : a≠0) :
    volume {u : ℝ | (u:ℂ)*a+b=0}=0 := by
  have hm : 0<‖a‖ := norm_pos_iff.mpr ha
  have hh := measure_zero_of_linear_sublevels volume
    (fun u : ℝ => ‖(u:ℂ)*a+b‖) (4/‖a‖) (by
      intro r hr
      convert complex_affine_parameter_sublevel a b ‖a‖ r hm le_rfl hr using 1
      congr 1
      ring)
  simpa only [norm_eq_zero] using hh

#print axioms complex_affine_parameter_sublevel
#print axioms complex_affine_parameter_inverse_sqrt
#print axioms complex_affine_parameter_zero_null

end QuantitativeMaass
