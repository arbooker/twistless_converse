module

public import FinitenessPaper2GrowthV1
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option autoImplicit false

public section

namespace FinitenessPaper2

open Filter Asymptotics FinitenessAllLevelLocalRoots

/-- Reciprocal-root bounds remove the individual implicit constant from
the recurrence, including when its two roots coincide. -/
theorem recurrence_coeff_bound (c : ℕ → ℂ) (a α β : ℂ)
    (hzero : c 0 = 1) (hone : c 1 = a)
    (hrec : ∀ n, c (n+2) = a*c (n+1)-c n)
    (hsum : α+β = a) (hprod : α*β = 1)
    {R : ℝ} (hR : 0 ≤ R) (ha : ‖α‖ ≤ R) (hb : ‖β‖ ≤ R) (n : ℕ) :
    ‖c n‖ ≤ (n+1 : ℝ)*R^n := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      have he : c (n+1) = α^(n+1)+β*c n := by
        linear_combination -(root_power c a α β hzero hone hrec hsum hprod n)
      calc
        ‖c (n+1)‖ ≤ ‖α^(n+1)‖+‖β*c n‖ := by rw [he]; exact norm_add_le _ _
        _ = ‖α‖^(n+1)+‖β‖*‖c n‖ := by rw [norm_pow, norm_mul]
        _ ≤ R^(n+1)+R*((n+1 : ℝ)*R^n) :=
          add_le_add (pow_le_pow_left₀ (norm_nonneg _) ha _)
            (mul_le_mul hb ih (norm_nonneg _) hR)
        _ = (((n+1 : ℕ) : ℝ)+1)*R^(n+1) := by push_cast; rw [pow_succ]; ring

theorem ramified_prime_norm_le_one {N k p : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) (hp : p.Prime) (hpN : p ∣ N) :
    ‖f p‖ ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hs : ‖f p‖^2 ≤ 1 := by
    rw [← norm_pow, hf.bad p hp hpN]
    split_ifs
    · simp
    · simpa only [norm_inv, Complex.norm_natCast] using (inv_le_one₀ hp0).mpr hp1
  nlinarith [norm_nonneg (f p)]

/-- Uniform prime-power coefficient bound for every prime, good or bad. -/
theorem prime_power_uniform_bound {N k p : ℕ} {σ : ℝ} {f : ℕ → ℂ}
    (hN : 0 < N) (hf : f ∈ E N k σ) (hp : p.Prime) (j : ℕ) :
    ‖f (p^j)‖ ≤ (j+1 : ℝ)*((p : ℝ)^σ)^j := by
  obtain ⟨ho, hg⟩ := (mem_iff_original N k σ f).mp hf
  have hσ := exponent_nonneg hN hf
  have hR1 : 1 ≤ (p : ℝ)^σ :=
    Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) hσ
  by_cases hpN : p ∣ N
  · rw [FinitenessEulerIdentification.bad_prime_power ho.zero hg ho.euler hp hpN j, norm_pow]
    have hb : ‖f p‖^j ≤ ((p : ℝ)^σ)^j :=
      pow_le_pow_left₀ (norm_nonneg _) ((ramified_prime_norm_le_one ho hp hpN).trans hR1) j
    have hr : 0 ≤ ((p : ℝ)^σ)^j := pow_nonneg (le_trans zero_le_one hR1) j
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  · obtain ⟨α, β, hsum, hprod, ha, hb⟩ := good_prime_roots ho hg hp hpN
    apply recurrence_coeff_bound (fun i => f (p^i)) (f p) α β
      (by simpa only [pow_zero] using (FinitenessEulerIdentification.solution_arithmetic ho).1)
      (by simp) _ hsum hprod (le_trans zero_le_one hR1) ha hb j
    intro n
    simpa only [ite_eq_right hpN, one_mul] using
      (FinitenessEulerIdentification.solution_arithmetic ho).2.2 p hp n

/-- Euler multiplicativity combines the uniform local bounds into the
literal divisor-function envelope used in the paper's compactness argument. -/
theorem coefficient_uniform_bound {N k : ℕ} {σ : ℝ} {f : ℕ → ℂ}
    (hN : 0 < N) (hf : f ∈ E N k σ) {n : ℕ} (hn : n ≠ 0) :
    ‖f n‖ ≤ (n.divisors.card : ℝ)*(n : ℝ)^σ := by
  classical
  obtain ⟨ho, hg⟩ := (mem_iff_original N k σ f).mp hf
  have he : f n = ∏ p ∈ n.primeFactors, f (p^(n.factorization p)) := by
    nth_rw 1 [FinitenessEulerIdentification.eq_canonical ho.zero hg ho.euler]
    simp only [FinitenessEulerCoefficients.value, ite_eq_right hn,
      Finsupp.prod, Nat.support_factorization]
    apply Finset.prod_congr rfl
    intro p hp
    have hc := congrFun (FinitenessEulerIdentification.eq_canonical ho.zero hg ho.euler)
      (p^(n.factorization p))
    rw [FinitenessEulerCoefficients.value_prime_pow _ _ (Nat.prime_of_mem_primeFactors hp)] at hc
    exact hc.symm
  have hfactor : (∏ p ∈ n.primeFactors, (p : ℝ)^(n.factorization p)) = n := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self hn
  rw [he, norm_prod]
  calc
    (∏ p ∈ n.primeFactors, ‖f (p^(n.factorization p))‖) ≤
        ∏ p ∈ n.primeFactors, (n.factorization p+1 : ℝ)*((p : ℝ)^σ)^(n.factorization p) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro p hp
      exact prime_power_uniform_bound hN hf (Nat.prime_of_mem_primeFactors hp) _
    _ = (∏ p ∈ n.primeFactors, (n.factorization p+1 : ℝ))*
        (∏ p ∈ n.primeFactors, ((p : ℝ)^(n.factorization p))^σ) := by
      simp only [Real.rpow_pow_comm (Nat.cast_nonneg _), Finset.prod_mul_distrib]
    _ = (n.divisors.card : ℝ)*(n : ℝ)^σ := by
      rw [Real.finsetProd_rpow _ _ (fun p _ => pow_nonneg (Nat.cast_nonneg p) _), hfactor]
      congr 1
      rw [Nat.card_divisors hn, Nat.cast_prod]
      simp only [Nat.cast_add, Nat.cast_one]

#print axioms recurrence_coeff_bound
#print axioms prime_power_uniform_bound
#print axioms coefficient_uniform_bound

end FinitenessPaper2
