module

public import FinitenessInputBoundsV1
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.Complex.AbsMax

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticQuadraticTwistQuotient

open Complex Set Metric

/-- A fixed circle around the sole small exponential zero has a uniform
positive denominator bound. No arithmetic assertion about zero locations is
assumed. -/
theorem exponential_circle_lower : ∃ δ : ℝ, 0 < δ ∧
    ∀ w : ℂ, ‖w‖ = 1 → δ ≤ ‖1 - exp w‖ := by
  have hn : (sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp⟩
  have hc : Continuous (fun w : ℂ => ‖1 - exp w‖) := by fun_prop
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMinOn hn hc.continuousOn
  have hw' : ‖w‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hw
  have hne : 1 - exp w ≠ 0 := by
    intro h
    have he : exp w = exp 0 := by simpa only [exp_zero] using (sub_eq_zero.mp h).symm
    have hw0 : w = 0 := exp_inj_of_neg_pi_lt_of_le_pi (x := w) (y := 0)
      (by have ht := (abs_le.mp (abs_im_le_norm w)).1; linarith [Real.two_le_pi])
      (by linarith [im_le_norm w, Real.two_le_pi])
      (by simpa using (neg_neg_of_pos Real.pi_pos))
      (by simpa using Real.pi_pos.le) he
    simp [hw0] at hw'
  refine ⟨‖1 - exp w‖, norm_pos_iff.mpr hne, ?_⟩
  intro v hv
  exact hmin (by simpa only [mem_sphere, dist_zero_right] using hv)

/-- If an exponential-linear denominator is small, its zero lies uniformly
nearby. The center is constructed using the principal logarithm. -/
theorem nearby_zero (a c z : ℂ) (ha : a ≠ 0)
    (hsmall : ‖1 - c * exp (a*z)‖ ≤ 1/4) :
    ∃ w : ℂ, c * exp (a*w) = 1 ∧ ‖z-w‖ ≤ (3/8) / ‖a‖ := by
  let h : ℂ := c * exp (a*z)
  have hnorm : ‖h-1‖ ≤ 1/4 := by
    simpa only [h, norm_sub_rev] using hsmall
  have hh : h ≠ 0 := by
    intro hz
    norm_num [hz] at hnorm
  have hlog : ‖log h‖ ≤ 3/8 := by
    have ht := norm_log_one_add_half_le_self (z := h-1) (by linarith)
    simp only [add_sub_cancel] at ht
    linarith
  refine ⟨z - log h / a, ?_, ?_⟩
  · rw [show a*(z-log h/a)=a*z-log h by field_simp,
      exp_sub, ← mul_div_assoc, exp_log hh]
    exact div_self hh
  · rw [show z-(z-log h/a)=log h/a by ring, norm_div]
    exact div_le_div_of_nonneg_right hlog (norm_nonneg a)

theorem denominator_at_zero (a c w v : ℂ) (hw : c * exp (a*w) = 1) :
    1 - c * exp (a*v) = 1 - exp (a*(v-w)) := by
  have he : exp (a*v) = exp (a*w) * exp (a*(v-w)) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he, ← mul_assoc, hw, one_mul]

#print axioms exponential_circle_lower
#print axioms nearby_zero
#print axioms denominator_at_zero

end QuantitativeArithmeticQuadraticTwistQuotient
