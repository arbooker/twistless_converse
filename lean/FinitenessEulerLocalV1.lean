module

public import FinitenessRamanujanFourierV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessEulerLocal

open Complex

/-- Coefficients of the reciprocal quadratic Euler factor. They are
constructed independently of the original f, not assumed equal to f(p^j). -/
def coeff (a b : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => a
  | n+2 => a*coeff a b (n+1)-b*coeff a b n

theorem coeff_bound (a b : ℂ) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖coeff a b n‖ ≤ (‖a‖+1)^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [coeff]
  | one => simp [coeff]
  | more n ih0 ih1 =>
      have ha : 0 ≤ ‖a‖ := norm_nonneg _
      have hL : 0 ≤ ‖a‖+1 := by positivity
      calc
        ‖coeff a b (n+2)‖ ≤ ‖a*coeff a b (n+1)‖+‖b*coeff a b n‖ := norm_sub_le _ _
        _ = ‖a‖*‖coeff a b (n+1)‖+‖b‖*‖coeff a b n‖ := by rw [norm_mul,norm_mul]
        _ ≤ ‖a‖*(‖a‖+1)^(n+1)+1*(‖a‖+1)^n :=
          add_le_add (mul_le_mul_of_nonneg_left ih1 ha)
            (mul_le_mul hb ih0 (norm_nonneg _) (by norm_num))
        _ ≤ (‖a‖+1)^(n+2) := by
          simp only [pow_add,pow_one,pow_two]
          nlinarith [mul_nonneg ha (pow_nonneg hL n)]

noncomputable def series (a b z : ℂ) (t : ℕ) : ℂ := ∑' n, coeff a b (n+t)*z^n

theorem summable_shift (a b z : ℂ) (hb : ‖b‖ ≤ 1)
    (hz : (‖a‖+1)*‖z‖ < 1) (t : ℕ) : Summable (fun n => coeff a b (n+t)*z^n) := by
  have hr0 : 0 ≤ (‖a‖+1)*‖z‖ := by positivity
  have hr : ‖(‖a‖+1)*‖z‖‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hz
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((summable_geometric_of_norm_lt_one hr).mul_left ((‖a‖+1)^t))
  intro n
  rw [norm_mul,norm_pow]
  calc
    ‖coeff a b (n+t)‖*‖z‖^n ≤ (‖a‖+1)^(n+t)*‖z‖^n :=
      mul_le_mul_of_nonneg_right (coeff_bound a b hb (n+t)) (by positivity)
    _ = (‖a‖+1)^t*((‖a‖+1)*‖z‖)^n := by rw [pow_add,mul_pow]; ring

theorem series_step (a b z : ℂ) (hb : ‖b‖ ≤ 1)
    (hz : (‖a‖+1)*‖z‖ < 1) (t : ℕ) :
    series a b z t=coeff a b t+z*series a b z (t+1) := by
  unfold series
  rw [(summable_shift a b z hb hz t).tsum_eq_zero_add]
  simp only [Nat.zero_add,pow_zero,mul_one]
  rw [← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  rw [show n+1+t=n+(t+1) by omega,pow_succ]
  ring

theorem series_recurrence (a b z : ℂ) (hb : ‖b‖ ≤ 1)
    (hz : (‖a‖+1)*‖z‖ < 1) :
    series a b z 2=a*series a b z 1-b*series a b z 0 := by
  unfold series
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← (summable_shift a b z hb hz 1 |>.mul_left a).tsum_sub
      (summable_shift a b z hb hz 0 |>.mul_left b)]
  apply tsum_congr
  intro n
  simp only [coeff,Nat.add_zero]
  ring

/-- Genuine convergent geometric expansion of the reciprocal quadratic,
including a proof that its denominator is nonzero in this disk. -/
theorem inverse_factor (a b z : ℂ) (hb : ‖b‖ ≤ 1)
    (hz : (‖a‖+1)*‖z‖ < 1) :
    (∑' n : ℕ, coeff a b n*z^n)=(1-a*z+b*z^2)⁻¹ := by
  have h0 := series_step a b z hb hz 0
  have h1 := series_step a b z hb hz 1
  have h2 := series_recurrence a b z hb hz
  simp only [coeff] at h0 h1
  have hm : (1-a*z+b*z^2)*series a b z 0=1 := by
    linear_combination (1-a*z)*h0+z*h1+z^2*h2
  have hd : 1-a*z+b*z^2 ≠ 0 := by intro h; rw [h,zero_mul] at hm; exact zero_ne_one hm
  have he : series a b z 0=1/(1-a*z+b*z^2) :=
    (eq_div_iff hd).mpr (by rw [mul_comm]; exact hm)
  simpa only [series,Nat.add_zero,one_div] using he

#print axioms coeff_bound
#print axioms inverse_factor

end FinitenessEulerLocal
