module

public import FinitenessAllLevelFormalGrowthV1
public import Mathlib.Analysis.Complex.TaylorSeries

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelTaylorGrowth

open Complex Metric Set FinitenessPolynomialSeries Function.Periodic

def taylor (G : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n G 0 / (n.factorial : ℂ)

theorem taylor_bound {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1))
    {r C : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ w ∈ sphere (0 : ℂ) r, ‖G w‖ ≤ C) (n : ℕ) :
    ‖taylor G n‖ ≤ C / r ^ n := by
  have hd := hG.diffContOnCl_ball (closedBall_subset_ball hr1)
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hd hC
  rw [taylor, norm_div, norm_natCast]
  calc
    _ ≤ ((n.factorial : ℝ) * C / r ^ n) / n.factorial :=
      div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)
    _ = C / r ^ n := by
      have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp

theorem taylor_polynomial {F G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1))
    (heq : ∀ z : ℂ, 0 < z.im → F z = G (qParam 1 z))
    {d : ℕ} {M : ℝ} (hb : ∀ z : ℂ, 0 < z.im → z.im ^ d * ‖F z‖ ≤ M)
    {n : ℕ} (hn : 0 < n) :
    ‖taylor G n‖ ≤ (M * Real.exp (2 * Real.pi)) * (n : ℝ) ^ d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hy : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
  have hr : 0 < Real.exp (-2 * Real.pi * (1 / (n : ℝ))) := Real.exp_pos _
  have hr1 : Real.exp (-2 * Real.pi * (1 / (n : ℝ))) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos hy])
  have h := taylor_bound hG hr hr1 (fun w hw =>
    FinitenessCuspBounds.circle_bound F G heq d hy hb
      (by simpa only [mem_sphere, dist_zero_right] using hw)) n
  have he : Real.exp (-2 * Real.pi * (1 / (n : ℝ))) ^ n = Real.exp (-2 * Real.pi) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [he, show -2 * Real.pi = -(2 * Real.pi) by ring, Real.exp_neg, div_pow, one_pow] at h
  convert h using 1
  field_simp

theorem polynomialBound {F G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1))
    (h0 : G 0 = 0) (heq : ∀ z : ℂ, 0 < z.im → F z = G (qParam 1 z))
    {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z : ℂ, 0 < z.im → z.im ^ d * ‖F z‖ ≤ M) :
    PolynomialBound (taylor G) := by
  refine ⟨M * Real.exp (2 * Real.pi), by positivity, d, fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    simp only [taylor, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, h0, norm_zero]
    positivity
  · exact (taylor_polynomial hG heq hb (Nat.pos_of_ne_zero hn)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

theorem sum_taylor {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    FinitenessPolynomialSeries.sum (taylor G) w = G w := by
  rw [FinitenessPolynomialSeries.sum_eq_tsum]
  convert Complex.taylorSeries_eq_on_ball' hw hG using 2
  funext n
  simp only [taylor, sub_zero, div_eq_mul_inv, mul_comm (iteratedDeriv n G 0)]

#print axioms taylor_bound
#print axioms taylor_polynomial
#print axioms polynomialBound
#print axioms sum_taylor

end FinitenessAllLevelTaylorGrowth
