module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public section

namespace QuantitativeHolomorphic

open Finset
open scoped BigOperators

/-- The loss product is controlled by the full reciprocal mass, without
the fixed fractional loss used by the older qualitative argument. -/
theorem contraction_product_le_exp {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) :
    (∏ i ∈ s, (1 - x i)) ≤ Real.exp (-(∑ i ∈ s, x i)) := by
  calc
    (∏ i ∈ s, (1 - x i)) ≤ ∏ i ∈ s, Real.exp (-x i) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact sub_nonneg.mpr (hx i hi).2
      · intro i _
        have h := Real.add_one_le_exp (-x i)
        linarith
    _ = Real.exp (-(∑ i ∈ s, x i)) := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib]

theorem affine_recurrence_product (e x : ℕ → ℝ) (T : ℝ)
    (hx : ∀ n, 0 ≤ x n ∧ x n ≤ 1)
    (he : ∀ n, e (n + 1) ≤ (1 - x n) * e n + x n * T) (n : ℕ) :
    e n ≤ T + (e 0 - T) * ∏ i ∈ range n, (1 - x i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      e (n + 1) ≤ (1 - x n) * e n + x n * T := he n
      _ ≤ (1 - x n) * (T + (e 0 - T) * ∏ i ∈ range n, (1 - x i)) + x n * T :=
        add_le_add (mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hx n).2)) le_rfl
      _ = T + (e 0 - T) * ∏ i ∈ range (n + 1), (1 - x i) := by
        rw [Finset.prod_range_succ]
        ring

theorem affine_recurrence_exp (e x : ℕ → ℝ) (T : ℝ) (hT : T ≤ e 0)
    (hx : ∀ n, 0 ≤ x n ∧ x n ≤ 1)
    (he : ∀ n, e (n + 1) ≤ (1 - x n) * e n + x n * T) (n : ℕ) :
    e n ≤ T + (e 0 - T) * Real.exp (-(∑ i ∈ range n, x i)) := by
  apply (affine_recurrence_product e x T hx he n).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (contraction_product_le_exp (range n) x (fun i _ => hx i))
    (sub_nonneg.mpr hT))

theorem reciprocal_loss_mem_unit_interval {p : ℕ} (hp : p.Prime)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) :
    0 ≤ σ / ((p : ℝ) - 1) ∧ σ / ((p : ℝ) - 1) ≤ 1 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hd : 0 < (p : ℝ) - 1 := by linarith
  exact ⟨div_nonneg hσ hd.le, (div_le_one hd).mpr (by linarith)⟩

/-- The precise reciprocal-sum hypothesis is kept visible.  Proving its
uniform logarithmic lower bound for the fresh primes is a separate
number-theoretic obligation. -/
theorem contraction_logarithmic_bound {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) {X b C : ℝ} (hX : 1 < X)
    (hmass : b * Real.log (Real.log X) - C ≤ ∑ i ∈ s, x i) :
    (∏ i ∈ s, (1 - x i)) ≤ Real.exp C * (Real.log X) ^ (-b) := by
  apply (contraction_product_le_exp s x hx).trans
  rw [Real.rpow_def_of_pos (Real.log_pos hX), ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

theorem prime_product_dvd (s : Finset ℕ) {D : ℕ}
    (hp : ∀ p ∈ s, p.Prime) (hd : ∀ p ∈ s, p ∣ D) : (∏ p ∈ s, p) ∣ D := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    rw [Finset.prod_insert hps]
    have hcop : p.Coprime (∏ q ∈ s, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply (Nat.coprime_primes (hp p (mem_insert_self _ _))
        (hp q (mem_insert_of_mem hq))).mpr
      intro heq
      exact hps (heq ▸ hq)
    exact hcop.mul_dvd_of_dvd_of_dvd (hd p (mem_insert_self _ _))
      (ih (fun q hq => hp q (mem_insert_of_mem hq))
        (fun q hq => hd q (mem_insert_of_mem hq)))

/-- Quantitative cost of excluding large prime divisors of the finite
denominator product.  Unlike a density assertion, this is an actual
finite arithmetic estimate, including the `log D / (Q log Q)` gain. -/
theorem excluded_prime_reciprocal_mass (s : Finset ℕ) {D : ℕ} (hD : 0 < D)
    (hp : ∀ p ∈ s, p.Prime) (hd : ∀ p ∈ s, p ∣ D)
    {Q : ℝ} (hQ : 1 < Q) (hlarge : ∀ p ∈ s, Q ≤ (p : ℝ)) :
    (∑ p ∈ s, 1 / ((p : ℝ) - 1)) ≤
      Real.log (D : ℝ) / ((Q - 1) * Real.log Q) := by
  have hQ0 : 0 < Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos hQ
  have hQ1 : 0 < Q - 1 := by linarith
  have hprod : (∏ p ∈ s, (p : ℝ)) ≤ (D : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hD (prime_product_dvd s hp hd)
  have hp0 : ∀ p ∈ s, 0 < (p : ℝ) := fun p h => lt_of_lt_of_le hQ0 (hlarge p h)
  have hlogs : (s.card : ℝ) * Real.log Q ≤ Real.log (D : ℝ) := by
    calc
      (s.card : ℝ) * Real.log Q = ∑ _p ∈ s, Real.log Q := by simp
      _ ≤ ∑ p ∈ s, Real.log (p : ℝ) :=
        sum_le_sum (fun p h => Real.log_le_log hQ0 (hlarge p h))
      _ = Real.log (∏ p ∈ s, (p : ℝ)) :=
        (Real.log_prod (fun p h => (hp0 p h).ne')).symm
      _ ≤ Real.log (D : ℝ) := Real.log_le_log (prod_pos hp0) hprod
  have hcard : (s.card : ℝ) ≤ Real.log (D : ℝ) / Real.log Q :=
    (le_div_iff₀ hlogQ).mpr hlogs
  calc
    (∑ p ∈ s, 1 / ((p : ℝ) - 1)) ≤ ∑ _p ∈ s, 1 / (Q - 1) := by
      apply sum_le_sum
      intro p h
      exact one_div_le_one_div_of_le hQ1 (by linarith [hlarge p h])
    _ = (s.card : ℝ) / (Q - 1) := by simp [div_eq_mul_inv]
    _ ≤ (Real.log (D : ℝ) / Real.log Q) / (Q - 1) :=
      div_le_div_of_nonneg_right hcard hQ1.le
    _ = Real.log (D : ℝ) / ((Q - 1) * Real.log Q) := by
      rw [div_div, mul_comm (Real.log Q)]

#print axioms contraction_product_le_exp
#print axioms affine_recurrence_exp
#print axioms contraction_logarithmic_bound
#print axioms prime_product_dvd
#print axioms excluded_prime_reciprocal_mass

end QuantitativeHolomorphic
