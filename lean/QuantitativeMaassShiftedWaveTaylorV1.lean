module

public import QuantitativeMaassWaveTaylorV1
public import QuantitativeMaassShiftedWaveScalarV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace QuantitativeMaass.Wave

/-- A fourth-order bound on the exceptional-spectrum branch. -/
theorem cosh_fourth_remainder {z : ℝ} (hz : |z| ≤ 1) :
    |Real.cosh z - (1 + z^2/2)| ≤ z^4 := by
  have hp := Real.exp_bound (n := 4) hz (by norm_num)
  have hm := Real.exp_bound (n := 4) (x := -z) (by simpa using hz) (by norm_num)
  norm_num [Finset.sum_range_succ, abs_pow] at hp hm
  rw [← abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ z^4)] at hp hm
  rw [Real.cosh_eq]
  have hp' := abs_le.mp hp
  have hm' := abs_le.mp hm
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (z^2)]

/-- Uniform small-time Taylor estimate for both spectral branches. -/
theorem signedCosine_fourth_remainder {t x : ℝ} (ht : |t| ≤ 1)
    (hx : -(1/4 : ℝ) ≤ x) :
    |signedCosine t x - (1-t^2*x/2)| ≤ 3*t^4*x^2 := by
  by_cases hx0 : 0 ≤ x
  · rw [signedCosine_nonneg_energy t x hx0]
    have hs := Real.sq_sqrt hx0
    have h := cosine_fourth_remainder (t*Real.sqrt x)
    have h2 : (t*Real.sqrt x)^2=t^2*x := by rw [mul_pow,hs]
    have h4 : (t*Real.sqrt x)^4=t^4*x^2 := by
      calc
        _ = ((t*Real.sqrt x)^2)^2 := by ring
        _ = _ := by rw [h2]; ring
    rw [h2,h4] at h
    simpa only [mul_assoc] using h
  · have hn : 0 ≤ -x := by linarith
    have hs := Real.sq_sqrt hn
    have hb : Real.sqrt (-x) ≤ 1 := (Real.sqrt_le_one).mpr (by linarith)
    have hz : |t*Real.sqrt (-x)|≤1 := by
      rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (mul_le_mul_of_nonneg_right ht (Real.sqrt_nonneg _)).trans (by simpa using hb)
    have h := cosh_fourth_remainder hz
    have h2 : (t*Real.sqrt (-x))^2= -(t^2*x) := by rw [mul_pow,hs]; ring
    have h4 : (t*Real.sqrt (-x))^4=t^4*x^2 := by
      calc
        _ = ((t*Real.sqrt (-x))^2)^2 := by ring
        _ = _ := by rw [h2]; ring
    rw [signedCosine_nonpos_energy t x (le_of_not_ge hx0)]
    rw [h2,h4] at h
    have he : 1 + -(t^2*x)/2 = 1-t^2*x/2 := by ring
    rw [he] at h
    exact h.trans (by nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ t^4) (sq_nonneg x)])

/-- The second-order estimate is uniform on the inverse spectrum near time zero. -/
theorem signedCosine_second_bound {t x : ℝ} (ht : |t| ≤ 1)
    (hx : -(1/4 : ℝ) ≤ x) :
    |signedCosine t x-1| ≤ 2*t^2*|x| := by
  by_cases hx0 : 0 ≤ x
  · rw [signedCosine_nonneg_energy t x hx0,abs_of_nonneg hx0]
    have h := cosine_second_bound (t*Real.sqrt x)
    rw [mul_pow,Real.sq_sqrt hx0] at h
    exact h.trans (by nlinarith [mul_nonneg (sq_nonneg t) hx0])
  · have ht2 : t^2 ≤ 1 := by nlinarith [sq_abs t,abs_nonneg t]
    have hx2 : x^2 ≤ (-x)/4 := by nlinarith
    have h4 := signedCosine_fourth_remainder ht hx
    have h := abs_sub_le (signedCosine t x) (1-t^2*x/2) 1
    have he : |1-t^2*x/2-1|=t^2*(-x)/2 := by
      rw [abs_of_nonneg (by nlinarith [mul_nonneg (sq_nonneg t) (show 0≤-x by linarith)])]
      ring
    rw [he] at h
    rw [abs_of_nonpos (le_of_not_ge hx0)]
    have hprod := mul_le_mul_of_nonneg_left hx2 (by positivity : (0:ℝ) ≤ t^4)
    have ht4 : t^4 ≤ t^2 := by nlinarith [sq_nonneg (t^2)]
    have hprod2 := mul_le_mul_of_nonneg_right ht4 (show 0≤-x by linarith)
    nlinarith

#print axioms cosh_fourth_remainder
#print axioms signedCosine_fourth_remainder
#print axioms signedCosine_second_bound

end QuantitativeMaass.Wave
