module

public import QuantitativeMaassComplexParameterSliceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- A real linear form cannot become small above the real axis unless
both of its real coefficients are small. The rectangle cost is explicit. -/
theorem real_linear_form_coefficient_bound (c d : ℝ) (z : ℂ) (X Y : ℝ)
    (hX : 0≤X) (hY : 0<Y) (hx : |z.re|≤X) (hy : Y≤z.im) :
    |c|+|d|≤(1+(X+1)/Y)*‖(c:ℂ)*z+d‖ := by
  have him : |c*z.im|≤‖(c:ℂ)*z+d‖ := by
    simpa only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero] using Complex.abs_im_le_norm ((c:ℂ)*z+d)
  have hre : |c*z.re+d|≤‖(c:ℂ)*z+d‖ := by
    simpa only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero] using Complex.abs_re_le_norm ((c:ℂ)*z+d)
  have hcy : |c| *Y≤‖(c:ℂ)*z+d‖ := by
    apply (mul_le_mul_of_nonneg_left hy (abs_nonneg c)).trans
    simpa only [abs_mul,abs_of_pos (hY.trans_le hy)] using him
  have hc : |c|≤‖(c:ℂ)*z+d‖/Y := (le_div_iff₀ hY).mpr hcy
  have hd0 : |d|≤|c*z.re+d|+|c*z.re| := by
    simpa only [sub_zero,zero_sub,abs_neg,add_sub_cancel_left] using
      abs_sub_le (c*z.re+d) 0 (c*z.re)
  have hd : |d|≤‖(c:ℂ)*z+d‖+|c| *X := by
    apply hd0.trans
    rw [abs_mul]
    exact add_le_add hre (mul_le_mul_of_nonneg_left hx (abs_nonneg c))
  calc
    _≤‖(c:ℂ)*z+d‖+|c| *(X+1) := by nlinarith
    _≤‖(c:ℂ)*z+d‖+(‖(c:ℂ)*z+d‖/Y)*(X+1) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (by positivity : 0≤X+1))
    _=_ := by ring

/-- A determinant-one companion row with bounded entries gives a uniform
polynomial lower bound for a real linear form on a retained rectangle. -/
theorem real_linear_form_lower_of_det (c d e f : ℝ) (hdet : c*f-d*e=1)
    (B : ℝ) (hB : 0<B) (he : |e|≤B) (hf : |f|≤B)
    (z : ℂ) (X Y : ℝ) (hX : 0≤X) (hY : 0<Y) (hx : |z.re|≤X) (hy : Y≤z.im) :
    1/(B*(1+(X+1)/Y))≤‖(c:ℂ)*z+d‖ := by
  have hrow : 1≤B*(|c|+|d|) := by
    calc
      _=|c*f-d*e| := by rw [hdet,abs_one]
      _≤|c*f|+|d*e| := by
        simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (c*f) 0 (d*e)
      _=|c| *|f|+|d| *|e| := by rw [abs_mul,abs_mul]
      _≤|c| *B+|d| *B := add_le_add
        (mul_le_mul_of_nonneg_left hf (abs_nonneg c))
        (mul_le_mul_of_nonneg_left he (abs_nonneg d))
      _=_ := by ring
  have hb := mul_le_mul_of_nonneg_left
    (real_linear_form_coefficient_bound c d z X Y hX hY hx hy) hB.le
  apply (div_le_iff₀ (by positivity : 0<B*(1+(X+1)/Y))).mpr
  nlinarith [hrow.trans hb]

#print axioms real_linear_form_coefficient_bound
#print axioms real_linear_form_lower_of_det

end QuantitativeMaass
