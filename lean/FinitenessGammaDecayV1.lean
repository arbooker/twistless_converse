module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace FinitenessGammaDecay

open Complex MeasureTheory Set

/-- The defining integral bounds Gamma on every positive vertical line. -/
theorem norm_le_real {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, GammaIntegral, Real.Gamma_eq_integral hs]
  calc
    ‖∫ x : ℝ in Ioi 0, ↑(Real.exp (-x)) * (x : ℂ)^(s-1)‖
        ≤ ∫ x : ℝ in Ioi 0, ‖↑(Real.exp (-x)) * (x : ℂ)^(s-1)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ in Ioi 0, Real.exp (-x) * x^(s.re-1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [sub_re, one_re]

/-- Arbitrarily high polynomial vertical decay from the Gamma recurrence.
No Stirling estimate or asymptotic expansion is required. -/
theorem weighted_bound (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    |s.im|^n * ‖Gamma s‖ ≤ Real.Gamma (s.re+(n : ℝ)) := by
  induction n generalizing s with
  | zero => simpa only [pow_zero, one_mul, Nat.cast_zero, add_zero] using norm_le_real hs
  | succ n ih =>
      have hs0 : s ≠ 0 := by intro hh; simp [hh] at hs
      have hs1 : 0 < (s+1).re := by simpa only [add_re, one_re] using (by linarith : 0<s.re+1)
      have hrec : ‖Gamma (s+1)‖ = ‖s‖*‖Gamma s‖ := by rw [Gamma_add_one s hs0, norm_mul]
      calc
        |s.im|^(n+1) * ‖Gamma s‖ = |s.im|^n * (|s.im| * ‖Gamma s‖) := by rw [pow_succ]; ring
        _ ≤ |s.im|^n * (‖s‖*‖Gamma s‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm s) (norm_nonneg _))
            (pow_nonneg (abs_nonneg _) _)
        _ = |(s+1).im|^n * ‖Gamma (s+1)‖ := by rw [hrec]; simp only [add_im, one_im, add_zero]
        _ ≤ Real.Gamma ((s+1).re+(n : ℝ)) := ih hs1
        _ = Real.Gamma (s.re+((n+1 : ℕ) : ℝ)) := by congr 1; simp only [add_re, one_re, Nat.cast_add_one]; ring

theorem vertical_line (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (t : ℝ) :
    |t|^n * ‖Gamma ((σ : ℂ)+(t : ℂ)*I)‖ ≤ Real.Gamma (σ+(n : ℝ)) := by
  simpa using weighted_bound n (s := (σ : ℂ)+(t : ℂ)*I) (by simpa using hσ)

#print axioms norm_le_real
#print axioms weighted_bound
#print axioms vertical_line

end FinitenessGammaDecay
