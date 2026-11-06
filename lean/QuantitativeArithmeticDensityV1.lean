module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic

open Finset Filter

/-- Number of primes below `n` failing `P`, viewed as a real number. -/
def badPrimeCount (P : ℕ → Prop) (n : ℕ) : ℝ := by
  classical
  exact ((n.primesBelow.filter (fun p => ¬ P p)).card : ℝ)

theorem badPrimeCount_eq (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    badPrimeCount P n = ((n.primesBelow.filter (fun p => ¬ P p)).card : ℝ) := by
  unfold badPrimeCount
  congr 2
  exact filter_congr_decidable _ _ _

/-- Ordinary relative density one among primes, expressed without division.
This definition does not assert density for any shifted-divisor predicate. -/
def RelativePrimeDensityOne (P : ℕ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    badPrimeCount P n ≤ ε * (n.primesBelow.card : ℝ)

theorem badPrimeCount_mono {P Q : ℕ → Prop}
    (hPQ : ∀ p, P p → Q p) (n : ℕ) :
    badPrimeCount Q n ≤ badPrimeCount P n := by
  classical
  rw [badPrimeCount_eq, badPrimeCount_eq]
  exact_mod_cast card_le_card (show
    n.primesBelow.filter (fun p => ¬ Q p) ⊆
      n.primesBelow.filter (fun p => ¬ P p) from by
    intro p hp
    obtain ⟨hp, hq⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hp, fun h => hq (hPQ p h)⟩)

theorem badPrimeCount_and_le (P Q : ℕ → Prop) (n : ℕ) :
    badPrimeCount (fun p => P p ∧ Q p) n ≤
      badPrimeCount P n + badPrimeCount Q n := by
  classical
  have hs : n.primesBelow.filter (fun p => ¬ (P p ∧ Q p)) ⊆
      n.primesBelow.filter (fun p => ¬ P p) ∪
        n.primesBelow.filter (fun p => ¬ Q p) := by
    intro p hp
    obtain ⟨hp, hpq⟩ := mem_filter.mp hp
    by_cases hP : P p
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hp, fun hQ => hpq ⟨hP, hQ⟩⟩))
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hp, hP⟩))
  have hc := (card_le_card hs).trans (card_union_le _ _)
  rw [badPrimeCount_eq, badPrimeCount_eq, badPrimeCount_eq]
  exact_mod_cast hc

theorem relativePrimeDensityOne_mono {P Q : ℕ → Prop}
    (hP : RelativePrimeDensityOne P) (hPQ : ∀ p, P p → Q p) :
    RelativePrimeDensityOne Q := by
  intro ε hε
  filter_upwards [hP ε hε] with n hn
  exact (badPrimeCount_mono hPQ n).trans hn

theorem relativePrimeDensityOne_true : RelativePrimeDensityOne (fun _ => True) := by
  classical
  intro ε hε
  filter_upwards [] with n
  simp only [badPrimeCount, not_true_eq_false, filter_false, card_empty, Nat.cast_zero]
  positivity

/-- The union bound proves closure under intersection; neither input is
silently promoted from positive density to density one. -/
theorem relativePrimeDensityOne_and {P Q : ℕ → Prop}
    (hP : RelativePrimeDensityOne P) (hQ : RelativePrimeDensityOne Q) :
    RelativePrimeDensityOne (fun p => P p ∧ Q p) := by
  intro ε hε
  filter_upwards [hP (ε / 2) (by linarith), hQ (ε / 2) (by linarith)] with n hnP hnQ
  have hbound := badPrimeCount_and_le P Q n
  linarith

/-- The finitely many residue classes and shifted-divisor requirements may
be intersected without introducing a progression-density loss. -/
theorem relativePrimeDensityOne_finset {ι : Type*} (s : Finset ι)
    (P : ι → ℕ → Prop) (hP : ∀ i ∈ s, RelativePrimeDensityOne (P i)) :
    RelativePrimeDensityOne (fun p => ∀ i ∈ s, P i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using relativePrimeDensityOne_true
  | @insert i s hi ih =>
    have hPi := hP i (mem_insert_self i s)
    have hPs := ih (fun j hj => hP j (mem_insert_of_mem hj))
    simpa only [mem_insert, forall_eq_or_imp] using relativePrimeDensityOne_and hPi hPs

/-- Removing a fixed finite set preserves density one. The only prime
distribution input here is infinitude of primes, via `primeCounting'`. -/
theorem relativePrimeDensityOne_notMem (S : Finset ℕ) :
    RelativePrimeDensityOne (fun p => p ∉ S) := by
  classical
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt ((S.card : ℝ) / ε)
  have hSK : (S.card : ℝ) ≤ ε * (K : ℝ) := by
    have hh := (div_lt_iff₀ hε).mp hK
    nlinarith
  filter_upwards [Nat.tendsto_primeCounting'.eventually (eventually_ge_atTop K)] with n hn
  have hKn : (K : ℝ) ≤ (n.primesBelow.card : ℝ) := by
    rw [Nat.primesBelow_card_eq_primeCounting']
    exact_mod_cast hn
  have hbad : badPrimeCount (fun p => p ∉ S) n ≤ (S.card : ℝ) := by
    rw [badPrimeCount_eq]
    norm_cast
    apply card_le_card
    intro p hp
    exact not_not.mp (mem_filter.mp hp).2
  exact hbad.trans (hSK.trans (mul_le_mul_of_nonneg_left hKn (le_of_lt hε)))

theorem relativePrimeDensityOne_remove_finset {P : ℕ → Prop}
    (hP : RelativePrimeDensityOne P) (S : Finset ℕ) :
    RelativePrimeDensityOne (fun p => P p ∧ p ∉ S) :=
  relativePrimeDensityOne_and hP (relativePrimeDensityOne_notMem S)

/-- Literal positive-divisor condition appearing in Bettin et al., Lemma 4.9.
Integer divisibility avoids truncating `p - Q` below the fixed shift.
The analytic assertion that this predicate has density one is NOT proved here. -/
def ShiftedDivisorClasses (Q M p : ℕ) : Prop :=
  ∀ a : ℕ, a < M → Nat.Coprime a M →
    ∃ d : ℕ, 0 < d ∧ (d : ℤ) ∣ ((p : ℤ) - (Q : ℤ)) ∧ Nat.ModEq M d a

#print axioms relativePrimeDensityOne_finset
#print axioms relativePrimeDensityOne_notMem
#print axioms relativePrimeDensityOne_remove_finset

end QuantitativeArithmetic
