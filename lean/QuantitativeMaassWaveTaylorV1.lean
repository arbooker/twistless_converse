module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeMaass.Wave

/-- A global fourth-order cosine remainder, with a deliberately coarse
constant. This remains uniform at high quotient frequencies. -/
theorem cosine_fourth_remainder (z : ℝ) :
    |Real.cos z-(1-z^2/2)|≤3*z^4 := by
  by_cases hz : |z|≤1
  · have h := Real.cos_bound hz
    rw [← abs_pow] at h
    have hz4 : |z^4|=z^4 := abs_of_nonneg (by positivity)
    rw [hz4] at h
    nlinarith [sq_nonneg (z^2)]
  · have hz1 : 1 < |z| := lt_of_not_ge hz
    have hz2 : 1≤z^2 := by nlinarith [sq_abs z]
    have h := abs_sub_le (Real.cos z) 0 (1-z^2/2)
    have hc := Real.abs_cos_le_one z
    have hp : |1-z^2/2|≤1+z^2/2 := by
      exact abs_le.mpr ⟨by linarith [sq_nonneg z],by linarith [sq_nonneg z]⟩
    simp only [sub_zero,zero_sub,abs_neg] at h
    nlinarith [sq_nonneg (z^2-1)]

/-- Uniform quadratic difference bound, derived from the half-angle
identity and the global sine bound. -/
theorem cosine_second_bound (z : ℝ) : |Real.cos z-1|≤z^2/2 := by
  have hs := Real.abs_sin_le_abs (x := z/2)
  have hsq : (Real.sin (z/2))^2≤(z/2)^2 := by
    nlinarith [sq_abs (Real.sin (z/2)),sq_abs (z/2),abs_nonneg (Real.sin (z/2)),abs_nonneg (z/2)]
  have hc : Real.cos z=1-2*(Real.sin (z/2))^2 := by
    have h := Real.cos_two_mul (z/2)
    have hs := Real.sin_sq_add_cos_sq (z/2)
    have hz : 2*(z/2)=z := by ring
    rw [hz] at h
    linarith
  rw [hc]
  have he : 1-2*(Real.sin (z/2))^2-1= -(2*(Real.sin (z/2))^2) := by ring
  rw [he,abs_neg,abs_of_nonneg (by positivity)]
  nlinarith

#print axioms cosine_fourth_remainder
#print axioms cosine_second_bound

end QuantitativeMaass.Wave
