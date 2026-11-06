module

public import AsymptoticGammaMomentsV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCappedGamma

open MeasureTheory Set AsymptoticGammaTail AsymptoticGammaMoments

theorem cap_ratio_sub_one_abs_le {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (t : ℕ) :
    |(min (a*x) 1)^t / (min a 1)^t - 1| ≤ |x^t - 1| := by
  have hc : 0 < min a 1 := lt_min ha zero_lt_one
  have hct : 0 < (min a 1)^t := pow_pos hc t
  have hax : 0 ≤ min (a*x) 1 := le_min (mul_nonneg ha.le hx) zero_le_one
  by_cases h1 : 1 ≤ x
  · have hlow : min a 1 ≤ min (a*x) 1 := by
      apply min_le_min _ le_rfl
      nlinarith
    have hupp : min (a*x) 1 ≤ x * min a 1 := by
      by_cases ha1 : a ≤ 1
      · rw [min_eq_left ha1, mul_comm x a]
        exact min_le_left _ _
      · rw [min_eq_right (le_of_not_ge ha1), mul_one]
        exact (min_le_right _ _).trans h1
    have hp := pow_le_pow_left₀ hax hupp t
    rw [mul_pow] at hp
    have hl : 1 ≤ (min (a*x) 1)^t / (min a 1)^t :=
      (one_le_div hct).mpr (pow_le_pow_left₀ hc.le hlow t)
    have hu : (min (a*x) 1)^t / (min a 1)^t ≤ x^t :=
      (div_le_iff₀ hct).mpr hp
    rw [abs_of_nonneg (sub_nonneg.mpr hl), abs_of_nonneg (sub_nonneg.mpr (hl.trans hu))]
    linarith
  · have hx1 : x ≤ 1 := le_of_not_ge h1
    have hupp : min (a*x) 1 ≤ min a 1 := by
      apply min_le_min _ le_rfl
      nlinarith
    have hlow : x * min a 1 ≤ min (a*x) 1 := by
      apply le_min
      · have h := mul_le_mul_of_nonneg_left (min_le_left a 1) hx
        nlinarith
      · have h := mul_le_mul_of_nonneg_left (min_le_right a 1) hx
        nlinarith
    have hp := pow_le_pow_left₀ (mul_nonneg hx hc.le) hlow t
    rw [mul_pow] at hp
    have hl : x^t ≤ (min (a*x) 1)^t / (min a 1)^t :=
      (le_div_iff₀ hct).mpr hp
    have hu : (min (a*x) 1)^t / (min a 1)^t ≤ 1 :=
      (div_le_one hct).mpr (pow_le_pow_left₀ hax hupp t)
    rw [abs_of_nonpos (sub_nonpos.mpr hu), abs_of_nonpos (sub_nonpos.mpr (hl.trans hu))]
    linarith

/-- The capped weight divided by its value at the mean height. -/
noncomputable def ratio (m t : ℕ) (r ε y : ℝ) : ℝ :=
  (min (y/ε) 1)^t / (min (((m : ℝ)+1)/(r*ε)) 1)^t

theorem ratio_error_le (m t : ℕ) {r ε y : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hy : 0 ≤ y) :
    |ratio m t r ε y - 1| ≤ |(r*y/((m : ℝ)+1))^t - 1| := by
  have hm : (m : ℝ)+1 ≠ 0 := by positivity
  have he : (((m : ℝ)+1)/(r*ε)) * (r*y/((m : ℝ)+1)) = y/ε := by
    field_simp
  simpa only [he, ratio] using cap_ratio_sub_one_abs_le
    (by positivity : 0 < ((m : ℝ)+1)/(r*ε))
    (by positivity : 0 ≤ r*y/((m : ℝ)+1)) t

theorem ratio_error_integrable (m t : ℕ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    Integrable (fun y => (ratio m t r ε y - 1)^2 * kernel m r y)
      (volume.restrict (Ioi 0)) := by
  apply (squared_error_integrable m t hr).mono_nonneg
  · have hc : Continuous (fun y => (ratio m t r ε y - 1)^2 * kernel m r y) := by
      unfold ratio kernel
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg (sq_nonneg _) (kernel_nonneg m r hy.le)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    apply mul_le_mul_of_nonneg_right _ (kernel_nonneg m r hy.le)
    have h := pow_le_pow_left₀ (abs_nonneg _) (ratio_error_le m t hr hε hy.le) 2
    simpa only [sq_abs] using h

/-- Uniform in the Fourier frequency and the cap height: the mean-square
relative capped-weight error is O_t(1/(m+1)). -/
theorem ratio_squared_error_bound (m t : ℕ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    (∫ y in Ioi 0, (ratio m t r ε y - 1)^2 * kernel m r y) /
      (∫ y in Ioi 0, kernel m r y) ≤
      (((2*t).factorial : ℝ) - 1) / ((m : ℝ)+1) := by
  apply le_trans _ (squared_error_bound m t hr)
  apply div_le_div_of_nonneg_right _ (integral_kernel_pos m hr).le
  apply integral_mono_ae (ratio_error_integrable m t hr hε) (squared_error_integrable m t hr)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  apply mul_le_mul_of_nonneg_right _ (kernel_nonneg m r hy.le)
  have h := pow_le_pow_left₀ (abs_nonneg _) (ratio_error_le m t hr hε hy.le) 2
  simpa only [sq_abs] using h

#print axioms cap_ratio_sub_one_abs_le
#print axioms ratio_squared_error_bound

end AsymptoticCappedGamma
