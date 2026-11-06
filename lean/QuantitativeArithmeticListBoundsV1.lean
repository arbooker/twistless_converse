module
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
namespace QuantitativeArithmeticListBounds

/-- Check a property once on the list, instead of rechecking every indexed
lookup by a quadratic computation. -/
theorem getD_of_forall {α : Type*} (P : α → Prop) (d : α) (hd : P d)
    (l : List α) (hl : ∀ x∈l, P x) (n : ℕ) : P (l.getD n d) := by
  induction l generalizing n with
  | nil => simpa using hd
  | cons a l ih =>
    cases n with
    | zero => simpa using hl a (by simp)
    | succ n =>
      simpa using ih (fun x hx => hl x (by simp [hx])) n

#print axioms getD_of_forall
end QuantitativeArithmeticListBounds
