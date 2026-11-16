module

public import QuantitativeArithmeticRetainedPrimeChoiceV1

@[expose] public section

namespace SpanningCriterion

open GridPrimeParts GridAdmissibleGap GridLabelDetection
  QuantitativeArithmeticRetainedPrimeChoice

/-- The arithmetic criterion in Theorem `thm:spanning`, with the strict square
inequality written in natural numbers. -/
def Condition (N : ℕ) (P : Finset ℕ) : Prop :=
  ∀ s : ℕ, 2 < s → (∀ p ∈ P, p ∣ s) → levelPart N s < s^2

theorem exists_prime_choices {N G : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hcond : Condition N P) :
    ∃ p : Fin G → ℕ, ∀ a, 2 < labelOrder a → ¬ GoodLabel N a →
      p a ∈ P ∧ (p a).Prime ∧ ¬ p a ∣ labelOrder a := by
  classical
  have hex : ∀ a : Fin G, ∃ p : ℕ, 2 < labelOrder a → ¬ GoodLabel N a →
      p ∈ P ∧ p.Prime ∧ ¬ p ∣ labelOrder a := by
    intro a
    by_cases ha : 2 < labelOrder a ∧ ¬ GoodLabel N a
    · have hp : ∃ p ∈ P, ¬ p ∣ labelOrder a := by
        by_contra! hh
        exact ha.2 (hcond _ ha.1 hh)
      obtain ⟨p,hp,hs⟩ := hp
      exact ⟨p,fun _ _ => ⟨hp,hP p hp,hs⟩⟩
    · exact ⟨2,fun hh hg => False.elim (ha ⟨hh,hg⟩)⟩
  exact Classical.skolem.mp hex

theorem condition_of_product {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hlarge : N < (∏ p ∈ P, p)^2) :
    Condition N P := by
  intro s hs hps
  have hd := prime_product_dvd hP hps
  have hle := Nat.le_of_dvd (by omega : 0 < s) hd
  exact (Nat.le_of_dvd hN (part_dvd N _)).trans_lt
    (hlarge.trans_le (pow_le_pow_left' hle 2))

#print axioms exists_prime_choices
#print axioms condition_of_product

end SpanningCriterion
