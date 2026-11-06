module

public import FinitenessFourierConstructionV1
public import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false
@[expose] public section

namespace FinitenessAllLevelFourierGrowth

open Complex Metric FinitenessPolynomialSeries FinitenessFourierConstruction
  Function.Periodic FormalMultilinearSeries

/-- Cauchy's coefficient bound for the actual scalar Fourier power series. -/
theorem coefficient_bound {a : ℕ → ℂ} (ha : PolynomialBound a) {r C : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ w ∈ sphere (0 : ℂ) r, ‖FinitenessPolynomialSeries.sum a w‖ ≤ C) (n : ℕ) :
    ‖a n‖ ≤ C / r ^ n := by
  have hd : DiffContOnCl ℂ (FinitenessPolynomialSeries.sum a) (ball 0 r) :=
    (FinitenessPolynomialSeries.holomorphic ha).diffContOnCl_ball
      (by intro w hw; exact mem_ball.mpr ((mem_closedBall.mp hw).trans_lt hr1))
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hd hC
  have he : a = fun j => iteratedDeriv j (FinitenessPolynomialSeries.sum a) 0 / j.factorial :=
    ofScalars_series_injective ℂ ℂ
      ((has_series ha).eq_formalMultilinearSeries (has_series ha).analyticAt.hasFPowerSeriesAt)
  rw [congr_fun he n, norm_div, norm_natCast]
  calc
    _ ≤ ((n.factorial : ℝ) * C / r ^ n) / n.factorial :=
      div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)
    _ = C / r ^ n := by
      have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp

theorem coefficient_bound_at_height {a : ℕ → ℂ} (ha : PolynomialBound a)
    {d : ℕ} {M y : ℝ} (hy : 0 < y)
    (hbound : ∀ z : ℂ, 0 < z.im → z.im ^ d * ‖fourier a z‖ ≤ M) (n : ℕ) :
    ‖a n‖ ≤ (M / y ^ d) / Real.exp (-2 * Real.pi * y) ^ n := by
  apply coefficient_bound ha (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (by
    have h := mul_pos Real.pi_pos hy
    nlinarith))
  intro w hw
  have hwn : ‖w‖ = Real.exp (-2 * Real.pi * y) := by
    simpa only [mem_sphere, dist_zero_right] using hw
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (hwn.trans_ne (Real.exp_ne_zero _))
  have him : (invQParam 1 w).im = y := by
    rw [im_invQParam, hwn, Real.log_exp]
    field_simp
  have h := hbound (invQParam 1 w) (by simpa only [him] using hy)
  rw [him, fourier, qParam_right_inv (by norm_num : (1 : ℝ) ≠ 0) hw0] at h
  exact (le_div_iff₀ (pow_pos hy d)).mpr (by simpa only [mul_comm] using h)

/-- A polynomial bound at height zero gives the same integer exponent
for the unnormalized Fourier coefficients, by taking height 1/n. -/
theorem coefficient_polynomial {a : ℕ → ℂ} (ha : PolynomialBound a)
    {d : ℕ} {M : ℝ}
    (hbound : ∀ z : ℂ, 0 < z.im → z.im ^ d * ‖fourier a z‖ ≤ M)
    {n : ℕ} (hn : 0 < n) :
    ‖a n‖ ≤ (M * Real.exp (2 * Real.pi)) * (n : ℝ) ^ d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : Real.exp (-2 * Real.pi * (1 / (n : ℝ))) ^ n = Real.exp (-2 * Real.pi) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have h := coefficient_bound_at_height ha (one_div_pos.mpr hnR) hbound n
  rw [he, show -2 * Real.pi = -(2 * Real.pi) by ring,
    Real.exp_neg, div_pow, one_pow] at h
  convert h using 1
  field_simp

#print axioms coefficient_bound
#print axioms coefficient_bound_at_height
#print axioms coefficient_polynomial

end FinitenessAllLevelFourierGrowth
