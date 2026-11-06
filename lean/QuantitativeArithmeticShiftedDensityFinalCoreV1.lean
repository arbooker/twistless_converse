module

public import QuantitativeArithmeticDensityV1
public import QuantitativeArithmeticShiftedReciprocalV1
public import QuantitativeArithmeticShiftedSievePrimeLowerV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic

open Finset Filter
open scoped BigOperators

/-- Finite set union bound used in the shifted-prime density assembly. -/
theorem badPrimeCount_le_packet_avoidance (P : ℕ → Prop) (S : Finset ℕ)
    (Q n : ℕ)
    (hP : ∀ p l : ℕ, l ∈ S → (l : ℤ) ∣ ((p : ℤ) - (Q : ℤ)) → P p) :
    badPrimeCount P n ≤ badPrimeCount (fun p => p ∉ S) n +
      ((n.primesBelow.filter (fun p => p ∉ S ∧
        ∀ l ∈ S, ¬ (l : ℤ) ∣ ((p : ℤ) - (Q : ℤ)))).card : ℝ) := by
  classical
  have hs : n.primesBelow.filter (fun p => ¬ P p) ⊆
      n.primesBelow.filter (fun p => ¬ p ∉ S) ∪
      n.primesBelow.filter (fun p => p ∉ S ∧
        ∀ l ∈ S, ¬ (l : ℤ) ∣ ((p : ℤ) - (Q : ℤ))) := by
    intro p hp
    obtain ⟨hp, hnot⟩ := mem_filter.mp hp
    by_cases hmem : p ∈ S
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hp, by simpa using hmem⟩))
    · exact mem_union.mpr (Or.inr (mem_filter.mpr
        ⟨hp, hmem, fun l hl hdiv => hnot (hP p l hl hdiv)⟩))
  rw [badPrimeCount_eq, badPrimeCount_eq]
  exact_mod_cast (card_le_card hs).trans (card_union_le _ _)

/-- This assembly lemma is explicitly conditional on a finite-packet sieve
bound. The final module supplies that bound from the proved Selberg sieve. -/
theorem relativePrimeDensityOne_prime_shifted_class_of_packet_bound
    (Q M : ℕ) (hQ : 0 < Q) (hM : 0 < M) (a : ZMod M) (ha : IsUnit a)
    (hupper : ∀ (S : Finset ℕ), (∀ l ∈ S, l.Prime) →
      (∀ l ∈ S, ¬ (l : ℤ) ∣ (Q : ℤ)) →
      ∀ᶠ n : ℕ in atTop,
        ((n.primesBelow.filter (fun p => p ∉ S ∧
          ∀ l ∈ S, ¬ (l : ℤ) ∣ ((p : ℤ) - (Q : ℤ)))).card : ℝ) ≤
          65 * (∏ l ∈ S, (1 - 1 / ((l : ℝ) - 1))) *
            ((n : ℝ) / Real.log n)) :
    RelativePrimeDensityOne (fun p => ∃ l : ℕ,
      l.Prime ∧ (l : ZMod M) = a ∧ (l : ℤ) ∣ ((p : ℤ) - (Q : ℤ))) := by
  classical
  let : NeZero M := ⟨Nat.ne_of_gt hM⟩
  obtain ⟨c, hc, hlower⟩ := exists_absolute_primesBelow_lower
  intro ε hε
  obtain ⟨S, hS, hprod⟩ := exists_primeClass_packet_product_lt a ha
    (range (Q + 1)) (show 0 < ε * c / 130 by positivity)
  have hSQ : ∀ l ∈ S, ¬ (l : ℤ) ∣ (Q : ℤ) := by
    intro l hl hdiv
    have hdivNat : l ∣ Q := by exact_mod_cast hdiv
    have hle := Nat.le_of_dvd hQ hdivNat
    exact (hS l hl).2.2 (mem_range.mpr (by omega))
  have hSprime : ∀ l ∈ S, l.Prime := fun l hl => (hS l hl).1
  have hcoef : 65 * (∏ l ∈ S, (1 - 1 / ((l : ℝ) - 1))) ≤ (ε / 2) * c := by
    linarith
  filter_upwards [hupper S hSprime hSQ, hlower,
    relativePrimeDensityOne_notMem S (ε / 2) (by positivity),
    eventually_ge_atTop (2 : ℕ)] with n hn hlow hfinite hn2
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
  have hratio : 0 ≤ (n : ℝ) / Real.log n := by positivity
  have hsmall :
      ((n.primesBelow.filter (fun p => p ∉ S ∧
        ∀ l ∈ S, ¬ (l : ℤ) ∣ ((p : ℤ) - (Q : ℤ)))).card : ℝ) ≤
        (ε / 2) * (n.primesBelow.card : ℝ) := by
    calc
      _ ≤ 65 * (∏ l ∈ S, (1 - 1 / ((l : ℝ) - 1))) *
          ((n : ℝ) / Real.log n) := hn
      _ ≤ ((ε / 2) * c) * ((n : ℝ) / Real.log n) :=
        mul_le_mul_of_nonneg_right hcoef hratio
      _ = (ε / 2) * (c * (n : ℝ) / Real.log n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
  have hcount := badPrimeCount_le_packet_avoidance
    (fun p => ∃ l : ℕ, l.Prime ∧ (l : ZMod M) = a ∧
      (l : ℤ) ∣ ((p : ℤ) - (Q : ℤ))) S Q n (by
      intro p l hl hdiv
      exact ⟨l, (hS l hl).1, (hS l hl).2.1, hdiv⟩)
  linarith

#print axioms badPrimeCount_le_packet_avoidance
#print axioms relativePrimeDensityOne_prime_shifted_class_of_packet_bound

end QuantitativeArithmetic
