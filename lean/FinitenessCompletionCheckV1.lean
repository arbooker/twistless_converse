module

public import FinitenessOriginalTheoremV1

set_option autoImplicit false

public section

namespace FinitenessCompletionCheck

/-- Explicitly expand S to the original IsSolution predicate at the final
boundary. This adds no assumption and makes the semantic target visible. -/
theorem original_predicate (N : ℕ) (hN : 0<N) (h16 : ¬16 ∣ N)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p^2 ∣ N) :
    ∃ C : ℕ, 0<C ∧ ∀ k : ℕ, 0<k → Even k →
      {f : ℕ → ℂ | FinitenessOriginalInput.IsSolution N k f}.Finite ∧
      {f : ℕ → ℂ | FinitenessOriginalInput.IsSolution N k f}.ncard ≤ C*k :=
  FinitenessOriginalTheorem.even_weight N hN h16 hsq

#check @FinitenessOriginalTheorem.admissible_level
#check @FinitenessOriginalTheorem.even_weight
#check @original_predicate
#print axioms original_predicate

end FinitenessCompletionCheck
