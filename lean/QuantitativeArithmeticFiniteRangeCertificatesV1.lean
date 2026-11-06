module
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
namespace QuantitativeArithmeticFiniteRangeCertificates

/-- Join adjacent checked intervals. Balanced uses of this lemma assemble
large finite certificates without a single large case split. -/
theorem join (P : ℕ → Prop) (start m n : ℕ)
    (hleft : ∀ i<m, P (i+start))
    (hright : ∀ i<n, P (i+(start+m))) :
    ∀ i<m+n, P (i+start) := by
  intro i hi
  by_cases h : i<m
  · exact hleft i h
  · have hh := hright (i-m) (by omega)
    have he : i-m+(start+m)=i+start := by omega
    rwa [he] at hh

#print axioms join

/-- Transport a finite checked block to its interval in the global index. -/
theorem block_shift (P : ℕ → Prop) {start count : ℕ}
    (h : ∀ i : Fin count, P (start+i.val))
    (n : ℕ) (hl : start≤n) (hh : n<start+count) : P n := by
  have hi : n-start<count := by omega
  have he : start+(n-start)=n := by omega
  simpa only [he] using h ⟨n-start,hi⟩

/-- Join interval assertions independently of the selected data. -/
theorem block_join (P : ℕ → Prop) {lo mid hi : ℕ}
    (hleft : ∀ n, lo≤n → n<mid → P n)
    (hright : ∀ n, mid≤n → n<hi → P n)
    (n : ℕ) (hl : lo≤n) (hh : n<hi) : P n := by
  by_cases h : n<mid
  · exact hleft n hl h
  · exact hright n (by omega) hh

/-- A checked block also transports its index-dependent selection. -/
theorem selected_shift {α : Type*} (P : ℕ → α → Prop)
    (select : ℕ → α) {start count : ℕ}
    (h : ∀ i : Fin count, P (start+i.val) (select i.val))
    (n : ℕ) (hl : start≤n) (hh : n<start+count) :
    P n (select (n-start)) := by
  have hi : n-start<count := by omega
  have he : start+(n-start)=n := by omega
  simpa only [he] using h ⟨n-start,hi⟩

/-- Join checked selections using the same interval split as their dispatcher. -/
theorem selected_join {α : Type*} (P : ℕ → α → Prop)
    (left right : ℕ → α) {lo mid hi : ℕ}
    (hleft : ∀ n, lo≤n → n<mid → P n (left n))
    (hright : ∀ n, mid≤n → n<hi → P n (right n))
    (n : ℕ) (hl : lo≤n) (hh : n<hi) :
    P n (if n<mid then left n else right n) := by
  by_cases h : n<mid
  · simpa only [ite_eq_left h] using hleft n hl h
  · simpa only [ite_eq_right h] using hright n (by omega) hh

#print axioms block_shift
#print axioms block_join
#print axioms selected_shift
#print axioms selected_join


/-- A checked point is a certificate for an interval of length one. -/
theorem singleton {P : ℕ → Prop} (h : P 0) : ∀ i<1, P i := by
  intro i hi
  have hi0 : i=0 := Nat.lt_one_iff.mp hi
  subst i
  exact h

#print axioms singleton

end QuantitativeArithmeticFiniteRangeCertificates
