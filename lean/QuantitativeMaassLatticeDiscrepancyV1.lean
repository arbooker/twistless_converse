module

public import QuantitativeMaassParabolicLineProfileV1
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- One cell of the first-order sum/integral discrepancy, with no monotonicity
assumption on the complex profile. -/
theorem unit_cell_discrepancy (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (a : ℝ) :
    ‖f a-∫ x in a..a+1,f x‖≤∫ x in a..a+1,‖deriv f x‖ := by
  have hd : Continuous (deriv f) := (contDiff_one_iff_deriv.mp hf).2
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hw (x : ℝ) : HasDerivAt (fun t : ℝ => ((t-a-1:ℝ):ℂ)) 1 x := by
    simpa only [id_eq,Complex.ofReal_one] using (((hasDerivAt_id x).sub_const a).sub_const 1).ofReal_comp
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hw x) (fun x _ => (hdiff x).hasDerivAt)
    (continuous_const.intervalIntegrable a (a+1)) (hd.intervalIntegrable a (a+1))
  have he' : (∫ x in a..a+1,((x-a-1:ℝ):ℂ)*deriv f x)=f a-∫ x in a..a+1,f x := by
    simpa using he
  rw [←he']
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith : a≤a+1) _
    (hd.norm.intervalIntegrable a (a+1))
  filter_upwards with x hx
  have hb : ‖((x-a-1:ℝ):ℂ)‖≤1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_le]
    constructor <;> linarith [hx.1,hx.2]
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _)

/-- A C1 profile with integrable value and derivative has an absolutely
summable lattice restriction. Its discrepancy is bounded by total variation. -/
theorem integer_lattice_discrepancy (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (hd : Integrable (deriv f)) (a : ℝ) :
    Summable (fun n : ℤ => f (a+n)) ∧
      ‖(∑' n : ℤ,f (a+n))-∫ x,f x‖≤∫ x,‖deriv f x‖ := by
  let E : ℤ → ℂ := fun n => f (a+n)-∫ x in a+n..a+n+1,f x
  have hb (n : ℤ) : ‖E n‖≤∫ x in a+n..a+n+1,‖deriv f x‖ := unit_cell_discrepancy f hf (a+n)
  have hsum := hd.norm.hasSum_intervalIntegral a
  have hE : Summable E := hsum.summable.of_norm_bounded hb
  have hI := hi.hasSum_intervalIntegral a
  have hF : Summable (fun n : ℤ => f (a+n)) := by
    convert hE.add hI.summable using 1
    funext n
    simp only [E,sub_add_cancel]
  refine ⟨hF,?_⟩
  have he : (∑' n : ℤ,f (a+n))-∫ x,f x=∑' n,E n := by
    rw [show (∫ x,f x)=∑' n : ℤ,∫ x in a+n..a+n+1,f x from hI.tsum_eq.symm,
      ←Summable.tsum_sub hF hI.summable]
  rw [he]
  exact tsum_of_norm_bounded hsum hb

#print axioms unit_cell_discrepancy
#print axioms integer_lattice_discrepancy

end QuantitativeMaass
