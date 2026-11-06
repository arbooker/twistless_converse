module
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
@[expose] public section
namespace QuantitativeArithmeticIntervalCertificate
universe u

/-- Glue any certified property along a finite interval split. This one
lemma replaces the repeated case-split proofs in generated lookup trees. -/
theorem interval_union {α : Sort u} {P : ℕ → α → Prop}
    {lo mid hi : ℕ} {f g : ℕ → α}
    (hleft : ∀ n, lo ≤ n → n < mid → P n (f n))
    (hright : ∀ n, mid ≤ n → n < hi → P n (g n)) :
    ∀ n, lo ≤ n → n < hi → P n (if n < mid then f n else g n) := by
  intro n hn hh
  by_cases hm : n < mid
  · simpa only [ite_eq_left hm] using hleft n hn hm
  · simpa only [ite_eq_right hm] using hright n (Nat.le_of_not_gt hm) hh

theorem interval_shift {α : Sort u} {P : ℕ → α → Prop}
    {lo len : ℕ} {f : ℕ → α}
    (h : ∀ i, i < len → P (lo + i) (f i)) :
    ∀ n, lo ≤ n → n < lo + len → P n (f (n - lo)) := by
  intro n hn hh
  have hi : n - lo < len := by omega
  simpa only [Nat.add_sub_of_le hn] using h (n - lo) hi

#print axioms interval_union
#print axioms interval_shift
end QuantitativeArithmeticIntervalCertificate
