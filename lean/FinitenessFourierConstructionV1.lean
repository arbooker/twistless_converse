module

public import FinitenessPolynomialSeriesV1
public import FinitenessGrowthNormalizationV1
public import Mathlib.Analysis.Complex.Periodic

@[expose] public section

namespace FinitenessFourierConstruction

open FinitenessPolynomialSeries Function.Periodic Metric

noncomputable def fourier (a : ℕ → ℂ) (z : ℂ) : ℂ := sum a (qParam 1 z)

/-- Canonical disk extension, with no arbitrary coordinates outside |w|<1. -/
noncomputable def disk (a : ℕ → ℂ) (w : ℂ) : ℂ := if ‖w‖ < 1 then sum a w else 0

theorem q_periodic (z : ℂ) : qParam 1 (z+1) = qParam 1 z := by
  simp only [qParam, Complex.ofReal_one, div_one, mul_add, mul_one,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem periodic (a : ℕ → ℂ) (z : ℂ) : fourier a (z+1) = fourier a z := by
  rw [fourier, q_periodic]
  rfl

theorem fourier_eq_exp (a : ℕ → ℂ) (z : ℂ) :
    fourier a z = ∑' n : ℕ, a n * Complex.exp (2*Real.pi*Complex.I*(n : ℂ)*z) := by
  rw [fourier, sum_eq_tsum]
  apply tsum_congr
  intro n
  congr 1
  rw [qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem holomorphic {a : ℕ → ℂ} (ha : PolynomialBound a) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (fourier a) z := by
  have hq : qParam 1 z ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right] using norm_qParam_lt_one (by norm_num) hz
  exact ((FinitenessPolynomialSeries.holomorphic ha).differentiableAt
    (isOpen_ball.mem_nhds hq)).comp z (differentiable_qParam (h := 1) z)

theorem disk_holomorphic {a : ℕ → ℂ} (ha : PolynomialBound a) :
    DifferentiableOn ℂ (disk a) (ball 0 1) := by
  apply (FinitenessPolynomialSeries.holomorphic ha).congr
  intro w hw
  simp only [mem_ball, dist_zero_right] at hw
  simp only [disk, ite_eq_left hw]

theorem disk_zero {a : ℕ → ℂ} (ha0 : a 0 = 0) : disk a 0 = 0 := by
  simp only [disk, norm_zero, zero_lt_one, ite_true, FinitenessPolynomialSeries.zero ha0]

theorem disk_outside (a : ℕ → ℂ) {w : ℂ} (hw : 1 ≤ ‖w‖) : disk a w = 0 := by
  exact ite_eq_right (not_lt.mpr hw)

theorem disk_eq_fourier (a : ℕ → ℂ) {z : ℂ} (hz : 0 < z.im) :
    disk a (qParam 1 z) = fourier a z := by
  exact ite_eq_left (norm_qParam_lt_one (by norm_num) hz)

theorem coefficients_unique {a b : ℕ → ℂ} (ha : PolynomialBound a) (hb : PolynomialBound b)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (heq : ∀ z : ℂ, 0 < z.im → fourier a z = fourier b z) : a = b := by
  apply FinitenessPolynomialSeries.coefficients_unique ha hb
  intro w hw
  by_cases hw0 : w=0
  · subst w
    rw [FinitenessPolynomialSeries.zero ha0, FinitenessPolynomialSeries.zero hb0]
  have hwn : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  have hz : 0 < (invQParam 1 w).im := by
    rw [im_invQParam]
    exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (by norm_num) (by positivity))
      (Real.log_neg (norm_pos_iff.mpr hw0) hwn)
  simpa only [fourier, qParam_right_inv (by norm_num : (1:ℝ) ≠ 0) hw0]
    using heq (invQParam 1 w) hz

#print axioms holomorphic
#print axioms disk_holomorphic
#print axioms coefficients_unique

end FinitenessFourierConstruction
