module

public import QuantitativeMaassWaveCFCV1
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeMaass.Wave

theorem dampedFrequency_bound (s : ℝ) : |s| *Real.sqrt (s⁻¹-1)≤1 := by
  by_cases hs : s≤0
  · have h : s⁻¹-1≤0 := by have := inv_nonpos.mpr hs; linarith
    rw [Real.sqrt_eq_zero_of_nonpos h,mul_zero]
    norm_num
  have hs0 : 0<s := lt_of_not_ge hs
  by_cases hs1 : 1≤s
  · have h : s⁻¹-1≤0 := by
      have hi := (inv_le_one₀ hs0).mpr hs1
      linarith
    rw [Real.sqrt_eq_zero_of_nonpos h,mul_zero]
    norm_num
  have hslt : s<1 := lt_of_not_ge hs1
  have hi : 0≤s⁻¹-1 := by
    have h := (one_le_inv₀ hs0).mpr hslt.le
    linarith
  have hsq := Real.sq_sqrt hi
  have he : s^2*(s⁻¹-1)=s-s^2 := by field_simp [ne_of_gt hs0]
  rw [abs_of_pos hs0]
  have hprod : (s*Real.sqrt (s⁻¹-1))^2=s-s^2 := by rw [mul_pow,hsq,he]
  nlinarith [sq_nonneg s,Real.sqrt_nonneg (s⁻¹-1),mul_nonneg hs0.le (Real.sqrt_nonneg (s⁻¹-1))]

theorem dampedCosine_time_bound (t u s : ℝ) :
    ‖dampedCosine t s-dampedCosine u s‖≤|t-u| := by
  have h := Real.abs_cos_sub_cos_le (t*Real.sqrt (s⁻¹-1)) (u*Real.sqrt (s⁻¹-1))
  rw [← sub_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)] at h
  calc
    ‖dampedCosine t s-dampedCosine u s‖=
        |s| *|Real.cos (t*Real.sqrt (s⁻¹-1))-Real.cos (u*Real.sqrt (s⁻¹-1))| := by
      rw [dampedCosine,dampedCosine,← mul_sub,Real.norm_eq_abs,abs_mul]
    _ ≤ |s| *(|t-u| *Real.sqrt (s⁻¹-1)) := mul_le_mul_of_nonneg_left h (abs_nonneg s)
    _ = |t-u| *(|s| *Real.sqrt (s⁻¹-1)) := by ring
    _ ≤ |t-u| *1 := mul_le_mul_of_nonneg_left (dampedFrequency_bound s) (abs_nonneg _)
    _ = |t-u| := mul_one _

#print axioms dampedCosine_time_bound

end QuantitativeMaass.Wave
