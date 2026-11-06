module

public import FinitenessAllLevelMellinPairV1
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace FinitenessAllLevelMellinDirichlet

open Complex Filter Asymptotics Set MeasureTheory FinitenessPolynomialSeries
  FinitenessFourierConstruction FinitenessAllLevelAxisDecay

def rate (N : ℕ) : ℝ := 2 * Real.pi / Real.sqrt N

theorem rate_pos {N : ℕ} (hN : 0 < N) : 0 < rate N := by
  have hs := Real.sqrt_pos.mpr (show (0 : ℝ) < N by exact_mod_cast hN)
  unfold rate
  positivity

theorem axis_expansion {N : ℕ} (hN : 0 < N) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0 = 0) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => a (n + 1) * (Real.exp (-(rate N * (n + 1)) * t) : ℂ))
      (axis N a t) := by
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hs := FinitenessOriginalFourier.exp_summable (z := (((t / Real.sqrt N : ℝ) : ℂ) * I)) ha
    (by simpa only [mul_I_im, ofReal_re] using div_pos ht hsqrt)
  have he (n : ℕ) : a n * cexp (2 * Real.pi * I * (n : ℂ) *
      (((t / Real.sqrt N : ℝ) : ℂ) * I)) =
      a n * (Real.exp (-(rate N * n) * t) : ℂ) := by
    rw [ofReal_exp]
    congr 2
    calc
      _ = (2 * Real.pi * (n : ℂ) * (((t / Real.sqrt N : ℝ) : ℂ))) * (I * I) := by ring
      _ = _ := by rw [I_mul_I]; unfold rate; push_cast; ring
  have hfull : HasSum (fun n : ℕ => a n * (Real.exp (-(rate N * n) * t) : ℂ))
      (axis N a t) := by
    simpa only [axis, fourier_eq_exp, he] using hs.hasSum
  simpa only [Nat.cast_add, Nat.cast_one] using
    (hasSum_nat_add_iff 1 (f := fun n : ℕ => a n * (Real.exp (-(rate N * n) * t) : ℂ))).mpr
      (by simpa [ha0] using hfull)

/-- Mellin integration of the actual scaled Fourier series, including the
absolute-convergence premise needed for exchange of sum and integral. -/
theorem axis_mellin {N : ℕ} (hN : 0 < N) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0 = 0) {w : ℂ} (hw : 0 < w.re)
    (hs : Summable (fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ w.re)) :
    mellin (axis N a) w = Gamma w * (rate N : ℂ) ^ (-w) *
      ∑' n : ℕ, a (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-w) := by
  have hc := rate_pos hN
  have hsum : Summable (fun n : ℕ => ‖a (n + 1)‖ /
      (rate N * ((n + 1 : ℕ) : ℝ)) ^ w.re) := by
    simpa only [Real.mul_rpow hc.le (Nat.cast_nonneg _), div_mul_eq_div_div,
      div_right_comm] using hs.div_const ((rate N) ^ w.re)
  have h := hasSum_mellin (p := fun n : ℕ => rate N * ((n + 1 : ℕ) : ℝ))
    (fun _ => Or.inr (mul_pos hc (by positivity))) hw
    (fun t ht => by simpa only [Nat.cast_add, Nat.cast_one] using axis_expansion hN ha ha0 ht)
    hsum
  rw [← h.tsum_eq]
  have hterm (n : ℕ) : Gamma w * a (n + 1) / ((rate N * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ w =
      (Gamma w * (rate N : ℂ) ^ (-w)) * (a (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-w)) := by
    rw [ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le (Nat.cast_nonneg _)]
    simp only [ofReal_natCast, div_eq_mul_inv, mul_inv_rev, ← cpow_neg]
    ring
  simp only [hterm]
  rw [← tsum_mul_left]

theorem polynomial_growth {a : ℕ → ℂ} (ha : PolynomialBound a) :
    ∃ d : ℕ, a =O[atTop] (fun n : ℕ => (n : ℝ) ^ (d : ℝ)) := by
  obtain ⟨C, hC, d, hd⟩ := ha
  refine ⟨d, IsBigO.of_bound (2 * C) ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (1 : ℝ) ≤ (n : ℝ) ^ d := one_le_pow₀ hnR
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.rpow_natCast]
  exact (hd n).trans (by nlinarith)

theorem summable_norm_div {a : ℕ → ℂ} {τ : ℝ}
    (ha : a =O[atTop] (fun n : ℕ => (n : ℝ) ^ τ)) {u : ℝ} (hu : τ + 1 < u) :
    Summable (fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ u) := by
  have h := FinitenessInputBounds.absolute_convergence ha hu
  apply h.congr
  intro n
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ)),
    div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  push_cast
  ring

#print axioms axis_expansion
#print axioms axis_mellin
#print axioms polynomial_growth
#print axioms summable_norm_div

end FinitenessAllLevelMellinDirichlet
