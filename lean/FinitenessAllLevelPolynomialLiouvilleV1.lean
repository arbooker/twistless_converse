module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter Polynomial
open scoped Topology

/-- Cauchy's estimate forces all Taylor coefficients above the polynomial
growth exponent to vanish. -/
theorem iteratedDeriv_zero_of_polynomial_growth (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (hb : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ k)
    (n : ℕ) (hn : k < n) : iteratedDeriv n f 0 = 0 := by
  apply norm_le_zero_iff.mp
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  let A : ℝ := (n.factorial : ℝ) * C * 2 ^ k
  have hA : 0 ≤ A := by positivity
  let R : ℝ := max 1 (A / ε) + 1
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [le_max_left (1 : ℝ) (A / ε)]
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hlarge : A / ε < R := by dsimp [R]; linarith [le_max_right (1 : ℝ) (A / ε)]
  have hpow : R ^ (k + 1) ≤ R ^ n := pow_le_pow_right₀ hR1 (Nat.succ_le_of_lt hn)
  have hbase : (1 + R) ^ k ≤ (2 * R) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  calc
    ‖iteratedDeriv n f 0‖ ≤ (n.factorial : ℝ) * (C * (1 + R) ^ k) / R ^ n :=
      Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf.diffContOnCl
        (fun z hz => by
          have hz' : ‖z‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
          simpa only [hz'] using hb z)
    _ ≤ A / R := by
      apply (div_le_div_iff₀ (pow_pos hR n) hR).mpr
      calc
        _ ≤ (n.factorial : ℝ) * (C * (2 * R) ^ k) * R := by gcongr
        _ = A * R ^ (k + 1) := by dsimp [A]; rw [mul_pow, pow_succ]; ring
        _ ≤ A * R ^ n := mul_le_mul_of_nonneg_left hpow hA
    _ ≤ ε := (div_le_iff₀ hR).mpr (by nlinarith [(div_lt_iff₀ hε).mp hlarge])

/-- Generalized Liouville: an entire function with a polynomial norm bound
is the evaluation of an actual polynomial. -/
theorem polynomial_of_entire_growth (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (hb : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ k) :
    ∃ P : Polynomial ℂ, ∀ z, P.eval z = f z := by
  classical
  let c : ℕ → ℂ := fun n => iteratedDeriv n f 0 / n.factorial
  have hc (n : ℕ) (hn : k < n) : c n = 0 := by
    simp only [c, iteratedDeriv_zero_of_polynomial_growth f hf hC k hb n hn, zero_div]
  let P : Polynomial ℂ := ∑ n ∈ Finset.range (k + 1), Polynomial.C (c n) * Polynomial.X ^ n
  have heval (z : ℂ) : P.eval z = ∑ n ∈ Finset.range (k + 1), c n * z ^ n := by
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  have hnear : f =ᶠ[𝓝 (0 : ℂ)] (fun z => P.eval z) := by
    have hseries := (hf.analyticAt 0).hasFPowerSeriesAt.eventually_hasSum
    filter_upwards [hseries] with z hz
    have hz' : HasSum (fun n => c n * z ^ n) (f z) := by
      simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add, c] using hz
    have hfin : HasSum (fun n => c n * z ^ n) (∑ n ∈ Finset.range (k + 1), c n * z ^ n) := by
      apply hasSum_sum_of_ne_finset_zero
      intro n hn
      rw [hc n (by simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hn), zero_mul]
    exact hz'.unique (heval z ▸ hfin)
  have he : f = (fun z => P.eval z) :=
    (show AnalyticOnNhd ℂ f univ from fun z _ => hf.analyticAt z).eq_of_eventuallyEq
      (AnalyticOnNhd.eval_polynomial P) hnear
  exact ⟨P, fun z => (congrFun he z).symm⟩

#print axioms iteratedDeriv_zero_of_polynomial_growth
#print axioms polynomial_of_entire_growth

end FinitenessAllLevelPolynomialPresentation
