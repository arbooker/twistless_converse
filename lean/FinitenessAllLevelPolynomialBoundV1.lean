module

public import FinitenessAllLevelEigenvalueDegreeV1
public import Mathlib.Analysis.Complex.TaylorSeries

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelEigenvalueDegree

open Complex Polynomial Metric Set

theorem iteratedDeriv_eval (P : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => P.eval z) = fun z => (Polynomial.derivative^[n] P).eval z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext z
    exact Polynomial.deriv _

/-- Cauchy's estimate on the unit circle bounds every polynomial coefficient
by the same constant, independently of its degree. -/
theorem coefficient_bound (P : Polynomial ℂ) {M : ℝ}
    (hb : ∀ z ∈ sphere (0 : ℂ) 1, ‖P.eval z‖ ≤ M) (n : ℕ) : ‖P.coeff n‖ ≤ M := by
  have hd : DiffContOnCl ℂ (fun z => P.eval z) (ball 0 1) := P.differentiable.diffContOnCl
  have hn := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num : (0 : ℝ) < 1) hd hb
  rw [iteratedDeriv_eval] at hn
  change ‖(Polynomial.derivative^[n] P).eval 0‖ ≤ _ at hn
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative] at hn
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul, norm_mul, norm_natCast,
    one_pow, div_one] at hn
  exact (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))).mp hn

/-- A unit-circle bound and degree j give a global eigenvalue bound of
degree exactly j, with an explicit constant j+1. -/
theorem polynomial_bound (P : Polynomial ℂ) {j : ℕ} (hj : P.natDegree ≤ j)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ sphere (0 : ℂ) 1, ‖P.eval z‖ ≤ M) (z : ℂ) :
    ‖P.eval z‖ ≤ (j + 1 : ℝ) * M * (1 + ‖z‖) ^ j := by
  have he : P.eval z = ∑ i ∈ Finset.range (j + 1), P.coeff i * z ^ i := by
    conv_lhs => rw [P.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hj)]
    rw [eval_finsetSum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), ‖P.coeff i * z ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (j + 1), M * (1 + ‖z‖) ^ j := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow]
      apply mul_le_mul (coefficient_bound P hb i) _ (pow_nonneg (norm_nonneg _) _) hM
      exact (pow_le_pow_left₀ (norm_nonneg _) (by linarith) i).trans
        (pow_le_pow_right₀ (by linarith [norm_nonneg z]) (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = _ := by simp [mul_assoc]

theorem DegreeBound.global_bound {f : ℂ → ℂ} {j : ℕ} (hf : DegreeBound f j)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ M) (z : ℂ) :
    ‖f z‖ ≤ (j + 1 : ℝ) * M * (1 + ‖z‖) ^ j := by
  obtain ⟨P, hP, he⟩ := hf
  simpa only [he] using polynomial_bound P hP hM (by simpa only [he] using hb) z

#print axioms coefficient_bound
#print axioms polynomial_bound
#print axioms DegreeBound.global_bound

end FinitenessAllLevelEigenvalueDegree
