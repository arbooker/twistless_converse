module

public import FinitenessEulerLocalV1
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

set_option autoImplicit false

namespace FinitenessEulerCoefficients

open FinitenessEulerLocal

/-- Canonical multiplicative coefficients constructed from the local
quadratic factors. No identification with the original sequence is assumed. -/
noncomputable def value (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n=0 then 0 else n.factorization.prod (fun p j => coeff (a p) (b p) j)

@[simp] theorem value_zero (a b : ℕ → ℂ) : value a b 0=0 := by simp [value]

@[simp] theorem value_one (a b : ℕ → ℂ) : value a b 1=1 := by simp [value]

theorem value_prime_pow (a b : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    value a b (p^j)=coeff (a p) (b p) j := by
  simp only [value, pow_ne_zero _ hp.ne_zero, ite_false, hp.factorization_pow]
  exact Finsupp.prod_single_index (by rfl)

theorem multiplicative (a b : ℕ → ℂ) {m n : ℕ} (hc : m.Coprime n) :
    value a b (m*n)=value a b m*value a b n := by
  by_cases hm : m=0
  · simp [hm]
  by_cases hn : n=0
  · simp [hn]
  simp only [value, hm, hn, mul_ne_zero hm hn, ite_false]
  rw [Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index_of_disjoint hc.disjoint_primeFactors _

/-- A uniform power bound at primes gives the corresponding power bound
at every integer, with no divisor-function loss. -/
theorem value_bound (a b : ℕ → ℂ) (d : ℕ)
    (hb : ∀ p, p.Prime → ‖b p‖ ≤ 1)
    (ha : ∀ p, p.Prime → ‖a p‖+1 ≤ (p : ℝ)^d) (n : ℕ) :
    ‖value a b n‖ ≤ (n : ℝ)^d := by
  by_cases hn : n=0
  · simp only [hn,value_zero,norm_zero]
    positivity
  have he : (∏ p ∈ n.primeFactors, (p : ℝ)^(n.factorization p))=(n : ℝ) := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self hn
  simp only [value,hn,ite_false,Finsupp.prod,Nat.support_factorization,norm_prod]
  calc
    (∏ p ∈ n.primeFactors, ‖coeff (a p) (b p) (n.factorization p)‖)
        ≤ ∏ p ∈ n.primeFactors, ((p : ℝ)^d)^(n.factorization p) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      exact (coeff_bound (a p) (b p) (hb p hprime) _).trans
        (pow_le_pow_left₀ (by positivity) (ha p hprime) _)
    _ = (∏ p ∈ n.primeFactors, (p : ℝ)^(n.factorization p))^d := by
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro p _
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = (n : ℝ)^d := by rw [he]

theorem polynomial_bound (a b : ℕ → ℂ) (d : ℕ)
    (hb : ∀ p, p.Prime → ‖b p‖ ≤ 1)
    (ha : ∀ p, p.Prime → ‖a p‖+1 ≤ (p : ℝ)^d) :
    FinitenessPolynomialSeries.PolynomialBound (value a b) := by
  refine ⟨1,by norm_num,d,fun n => ?_⟩
  have h := value_bound a b d hb ha n
  linarith

theorem prime_bound {a : ℕ → ℂ}
    (ha : FinitenessPolynomialSeries.PolynomialBound a) :
    ∃ d : ℕ, ∀ p, p.Prime → ‖a p‖+1 ≤ (p : ℝ)^d := by
  obtain ⟨C,hC,d,hd⟩ := ha
  obtain ⟨u,hu⟩ := pow_unbounded_of_one_lt (2*C+1) (by norm_num : (1:ℝ)<2)
  refine ⟨u+d,fun p hp => ?_⟩
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1:ℝ) ≤ p := by linarith
  have hpd : (1:ℝ) ≤ (p:ℝ)^d := one_le_pow₀ hp1
  have hpu : 2*C+1 ≤ (p:ℝ)^u :=
    hu.le.trans (pow_le_pow_left₀ (by norm_num) hp2 u)
  calc
    ‖a p‖+1 ≤ (2*C+1)*(p:ℝ)^d := by
      have h := hd p
      nlinarith
    _ ≤ (p:ℝ)^u*(p:ℝ)^d := mul_le_mul_of_nonneg_right hpu (by positivity)
    _ = (p:ℝ)^(u+d) := (pow_add _ _ _).symm

theorem polynomial_bound_of_input {a b : ℕ → ℂ}
    (ha : FinitenessPolynomialSeries.PolynomialBound a)
    (hb : ∀ p, p.Prime → ‖b p‖ ≤ 1) :
    FinitenessPolynomialSeries.PolynomialBound (value a b) := by
  obtain ⟨d,hd⟩ := prime_bound ha
  exact polynomial_bound a b d hb hd

#print axioms value_prime_pow
#print axioms multiplicative
#print axioms value_bound
#print axioms polynomial_bound_of_input

end FinitenessEulerCoefficients
