module

public import QuantitativeHolomorphicPrimeMassV1
public import Mathlib.Algebra.BigOperators.Module

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open Finset Filter

/-- Abel summation transfers upper bounds for unweighted partial sums
to every nonnegative decreasing weight. -/
theorem weighted_sum_le_of_prefix_le (f w : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w) (n : ℕ)
    (hprefix : ∀ j ≤ n, ∑ i ∈ range j, f i ≤ C) :
    ∑ i ∈ range n, w i * f i ≤ C * w 0 := by
  by_cases hn : n = 0
  · simp only [hn, range_zero, sum_empty]
    exact mul_nonneg hC (hw0 0)
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hab := Finset.sum_range_by_parts w f n
    simp only [smul_eq_mul] at hab
    rw [hab]
    have hfirst : w (n - 1) * (∑ i ∈ range n, f i) ≤ w (n - 1) * C :=
      mul_le_mul_of_nonneg_left (hprefix n le_rfl) (hw0 _)
    have hsum : ∑ i ∈ range (n - 1), (w (i + 1) - w i) * C ≤
        ∑ i ∈ range (n - 1), (w (i + 1) - w i) * (∑ j ∈ range (i + 1), f j) := by
      apply sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonpos_left (hprefix (i + 1) (by have := mem_range.mp hi; omega))
      exact sub_nonpos.mpr (hw (Nat.le_succ i))
    calc
      _ ≤ w (n - 1) * C - ∑ i ∈ range (n - 1), (w (i + 1) - w i) * C := sub_le_sub hfirst hsum
      _ = C * w 0 := by
        rw [← sum_mul, sum_range_sub]
        ring

theorem weighted_prefix_comparison (a b w : ℕ → ℝ) {ε C : ℝ} (hC : 0 ≤ C)
    (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w) (n : ℕ)
    (hprefix : ∀ j ≤ n, (∑ i ∈ range j, a i) ≤ ε * (∑ i ∈ range j, b i) + C) :
    (∑ i ∈ range n, w i * a i) ≤ ε * (∑ i ∈ range n, w i * b i) + C * w 0 := by
  have hp : ∀ j ≤ n, (∑ i ∈ range j, (a i - ε * b i)) ≤ C := by
    intro j hj
    rw [sum_sub_distrib, ← mul_sum]
    linarith [hprefix j hj]
  have hh := weighted_sum_le_of_prefix_le (fun i => a i - ε * b i) w hC hw0 hw n hp
  simp only [mul_sub, sum_sub_distrib] at hh
  have he : (∑ i ∈ range n, w i * (ε * b i)) = ε * ∑ i ∈ range n, w i * b i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [he] at hh
  linarith

/-- Relative density in ordinary counting transfers to reciprocal
mass, up to a fixed additive constant.  This is unconditional Abel
summation; it does not assume or claim a shifted-divisor density theorem. -/
theorem eventual_prefix_comparison_weighted (a b w : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w) {ε : ℝ} (hε : 0 ≤ ε)
    (hcount : ∀ᶠ n in atTop, (∑ i ∈ range n, a i) ≤ ε * (∑ i ∈ range n, b i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      (∑ i ∈ range n, w i * a i) ≤ ε * (∑ i ∈ range n, w i * b i) + C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hcount
  let C := ∑ i ∈ range N, a i
  have hC : 0 ≤ C := sum_nonneg fun i _ => ha i
  refine ⟨C * w 0, mul_nonneg hC (hw0 _), ?_⟩
  intro n
  apply weighted_prefix_comparison a b w hC hw0 hw n
  intro j _
  by_cases hj : N ≤ j
  · exact (hN j hj).trans (le_add_of_nonneg_right hC)
  · have hjN : j ≤ N := le_of_not_ge hj
    have hsum : (∑ i ∈ range j, a i) ≤ C :=
      sum_le_sum_of_subset_of_nonneg (range_mono hjN) (fun i _ _ => ha i)
    exact hsum.trans (le_add_of_nonneg_left (mul_nonneg hε (sum_nonneg fun i _ => hb i)))

def primeReciprocalWeight (n : ℕ) : ℝ := 1 / max 1 ((n : ℝ) - 1)

theorem primeReciprocalWeight_nonneg (n : ℕ) : 0 ≤ primeReciprocalWeight n := by
  unfold primeReciprocalWeight
  positivity

theorem primeReciprocalWeight_antitone : Antitone primeReciprocalWeight := by
  intro m n hmn
  unfold primeReciprocalWeight
  apply one_div_le_one_div_of_le (by positivity)
  exact max_le_max le_rfl (by exact_mod_cast (show (m : ℝ) - 1 ≤ (n : ℝ) - 1 by exact sub_le_sub_right (by exact_mod_cast hmn) 1))

theorem primeReciprocalWeight_eq {p : ℕ} (hp : p.Prime) :
    primeReciprocalWeight p = 1 / ((p : ℝ) - 1) := by
  unfold primeReciprocalWeight
  rw [max_eq_right]
  have hh : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  linarith

theorem prime_weighted_indicator_sum (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    (∑ i ∈ range n, primeReciprocalWeight i * (if i.Prime ∧ P i then 1 else 0)) =
      ∑ p ∈ n.primesBelow.filter P, 1 / ((p : ℝ) - 1) := by
  rw [Nat.primesBelow_eq_filter_range, filter_filter, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p.Prime
  · simp only [hp, true_and, primeReciprocalWeight_eq hp]
    split_ifs <;> simp
  · simp [hp]

/-- Density one among primes implies a quantitative logarithmic
reciprocal mass lower bound.  Only the displayed ordinary counting
hypothesis is conditional; no prime-number theorem is used. -/
theorem good_prime_mass_of_count_density (P : ℕ → Prop) [DecidablePred P]
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hcount : ∀ᶠ n : ℕ in atTop,
      (((n.primesBelow.filter (fun p => ¬ P p)).card : ℕ) : ℝ) ≤
        ε * (n.primesBelow.card : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      (1 - ε) * Real.log (Real.log (n + 1 : ℝ)) - C ≤
        ∑ p ∈ (n + 1).primesBelow.filter P, 1 / ((p : ℝ) - 1) := by
  let a : ℕ → ℝ := fun p => if p.Prime ∧ ¬ P p then 1 else 0
  let b : ℕ → ℝ := fun p => if p.Prime then 1 else 0
  have hacount (n : ℕ) : (∑ i ∈ range n, a i) =
      ((n.primesBelow.filter (fun p => ¬ P p)).card : ℝ) := by
    simp [a, Nat.primesBelow_eq_filter_range, filter_filter]
  have hbcount (n : ℕ) : (∑ i ∈ range n, b i) = (n.primesBelow.card : ℝ) := by
    simp [b, Nat.primesBelow_eq_filter_range]
  have hc : ∀ᶠ n in atTop, (∑ i ∈ range n, a i) ≤ ε * ∑ i ∈ range n, b i := by
    simpa only [hacount, hbcount] using hcount
  obtain ⟨C, hC, hbound⟩ := eventual_prefix_comparison_weighted a b primeReciprocalWeight
    (fun i => by dsimp [a]; split_ifs <;> norm_num)
    (fun i => by dsimp [b]; split_ifs <;> norm_num)
    primeReciprocalWeight_nonneg primeReciprocalWeight_antitone hε hc
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hbad := hbound (n + 1)
  have haweight : (∑ i ∈ range (n + 1), primeReciprocalWeight i * a i) =
      ∑ p ∈ (n + 1).primesBelow.filter (fun p => ¬ P p), 1 / ((p : ℝ) - 1) :=
    prime_weighted_indicator_sum (fun p => ¬ P p) (n + 1)
  have hbweight : (∑ i ∈ range (n + 1), primeReciprocalWeight i * b i) =
      ∑ p ∈ (n + 1).primesBelow, 1 / ((p : ℝ) - 1) := by
    simpa [b] using prime_weighted_indicator_sum (fun _ => True) (n + 1)
  rw [haweight, hbweight] at hbad
  have hsplit := sum_filter_add_sum_filter_not (n + 1).primesBelow P
    (fun p : ℕ => 1 / ((p : ℝ) - 1))
  have hlower := loglog_le_prime_reciprocal_loss n hn
  simp only [Nat.cast_add, Nat.cast_one] at hlower
  have hh := mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr hε1)
  nlinarith

/-- The reciprocal-mass transfer gives the actual finite fresh-prime
contraction product, with every exponent and multiplicative constant
visible.  Supplying the good-prime counting theorem is still required. -/
theorem good_prime_product_of_count_density (P : ℕ → Prop) [DecidablePred P]
    {ε σ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hcount : ∀ᶠ n : ℕ in atTop,
      ((n.primesBelow.filter (fun p => ¬ P p)).card : ℝ) ≤
        ε * (n.primesBelow.card : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      (∏ p ∈ (n + 1).primesBelow.filter P, (1 - σ / ((p : ℝ) - 1))) ≤
        Real.exp C * (Real.log (n + 1 : ℝ)) ^ (-(σ * (1 - ε))) := by
  obtain ⟨C, hC, hmass⟩ := good_prime_mass_of_count_density P hε hε1 hcount
  refine ⟨σ * C, mul_nonneg hσ hC, ?_⟩
  intro n hn
  apply contraction_logarithmic_bound ((n + 1).primesBelow.filter P)
    (fun p => σ / ((p : ℝ) - 1)) ?_ (by exact_mod_cast (show 1 < n + 1 by omega))
  · have hh := mul_le_mul_of_nonneg_left (hmass n hn) hσ
    have he : (∑ p ∈ (n + 1).primesBelow.filter P, σ / ((p : ℝ) - 1)) =
        σ * ∑ p ∈ (n + 1).primesBelow.filter P, 1 / ((p : ℝ) - 1) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    rw [he]
    nlinarith
  · intro p hp
    exact reciprocal_loss_mem_unit_interval
      (Nat.prime_of_mem_primesBelow (mem_filter.mp hp).1) hσ hσ1

#print axioms weighted_sum_le_of_prefix_le
#print axioms eventual_prefix_comparison_weighted
#print axioms good_prime_mass_of_count_density
#print axioms good_prime_product_of_count_density

end QuantitativeHolomorphic
