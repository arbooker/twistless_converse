module

public import AsymptoticPrefixCongruenceLossV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open AsymptoticCompactObservationCount (Row)
open AsymptoticIntegralSubgroup

/-- The untwisted equation followed by the selected fresh-prime equations. -/
def primeRows (N : ℕ) (q : ℕ → ℕ) (hq : ∀ n,(q n).Prime) : ℕ → Row N
  | 0 => .twist 1 Nat.zero_lt_one
  | n+1 => .twist (q n) (hq n).pos

theorem primeRows_fresh (N : ℕ) (q : ℕ → ℕ) (hq : ∀ n,(q n).Prime)
    (hprev : ∀ m n,m<n → ¬q n∣q m) (n : ℕ) :
    ∀ i≤n,Fresh (q n) (primeRows N q hq i) := by
  intro i hi
  cases i with
  | zero => exact (hq n).not_dvd_one
  | succ i => exact hprev i n (by omega)

theorem primeRows_range_subset {N : ℕ} (r : ℕ → Row N)
    (hcover : ∀ q : ℕ,∀ hq : 0<q,∃ j,r j=.twist q hq)
    (q : ℕ → ℕ) (hq : ∀ n,(q n).Prime) :
    Set.range (primeRows N q hq)⊆Set.range r := by
  rintro _ ⟨i,rfl⟩
  cases i with
  | zero => exact hcover 1 Nat.zero_lt_one
  | succ i => exact hcover (q i) (hq i).pos

#print axioms primeRows_fresh
#print axioms primeRows_range_subset

end AsymptoticRegularObservation
