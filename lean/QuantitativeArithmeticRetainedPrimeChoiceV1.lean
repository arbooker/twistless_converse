module

public import GridSelectedWindowsV1
public import Mathlib.Data.Nat.GCD.BigOperators

@[expose] public section

namespace QuantitativeArithmeticRetainedPrimeChoice

open GridPrimeParts GridAdmissibleGap GridLabelDetection GridSelectedWindows

/-- Distinct prime divisors divide simultaneously. -/
theorem prime_product_dvd {P : Finset ℕ} {s : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hs : ∀ p ∈ P, p ∣ s) : (∏ p ∈ P, p) ∣ s := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    rw [Finset.prod_insert hp]
    have hp' : p.Prime := hP p (Finset.mem_insert_self _ _)
    have hc : Nat.Coprime p (∏ q ∈ P, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact hp'.coprime_iff_not_dvd.mpr (by
        intro hd
        have he := (hP q (Finset.mem_insert_of_mem hq)).eq_one_or_self_of_dvd p hd
        rcases he with he | he
        · exact hp'.ne_one he
        · exact hp (he ▸ hq))
    exact hc.mul_dvd_of_dvd_of_dvd (hs p (Finset.mem_insert_self _ _))
      (ih (fun q hq => hP q (Finset.mem_insert_of_mem hq))
        (fun q hq => hs q (Finset.mem_insert_of_mem hq)))

/-- A set of primes with product greater than `sqrt N` contains a prime
missing from every bad label order. The square formulation avoids roots. -/
theorem exists_prime_not_dvd {N s : ℕ} (P : Finset ℕ)
    (hN : 0 < N) (hP : ∀ p ∈ P, p.Prime) (hlarge : N < (∏ p ∈ P, p)^2)
    (hs : 0 < s) (hbad : s^2 ≤ levelPart N s) : ∃ p ∈ P, ¬ p ∣ s := by
  classical
  by_contra! h
  have hd := prime_product_dvd hP h
  have hle := Nat.le_of_dvd hs hd
  have hn : levelPart N s ≤ N := Nat.le_of_dvd hN (part_dvd N _)
  exact (not_le_of_gt hlarge) ((pow_le_pow_left' hle 2).trans (hbad.trans hn))

def GoodLabel (N : ℕ) {G : ℕ} (a : Fin G) : Prop :=
  levelPart N (labelOrder a) < (labelOrder a)^2

theorem exists_prime_choices {N G : ℕ} (hN : 0 < N) (hG : 0 < G)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hlarge : N < (∏ p ∈ P, p)^2) :
    ∃ p : Fin G → ℕ, ∀ a, ¬ GoodLabel N a →
      p a ∈ P ∧ (p a).Prime ∧ ¬ p a ∣ labelOrder a := by
  classical
  have hex : ∀ a : Fin G, ∃ p : ℕ, ¬ GoodLabel N a →
      p ∈ P ∧ p.Prime ∧ ¬ p ∣ labelOrder a := by
    intro a
    by_cases ha : GoodLabel N a
    · exact ⟨2, fun hn => False.elim (hn ha)⟩
    · obtain ⟨p,hp,hs⟩ := exists_prime_not_dvd P hN hP hlarge
        (label_order_pos hG a) (Nat.le_of_not_gt ha)
      exact ⟨p,fun _ => ⟨hp,hP p hp,hs⟩⟩
  exact Classical.skolem.mp hex

#print axioms prime_product_dvd
#print axioms exists_prime_not_dvd
#print axioms exists_prime_choices

end QuantitativeArithmeticRetainedPrimeChoice
