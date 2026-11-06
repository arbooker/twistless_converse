module

public import FinitenessEulerIndependenceV1
public import FinitenessEulerRecurrenceV1

set_option autoImplicit false

public section

namespace FinitenessEulerFamily

variable {I K : Type*} [Field K]

/-- Distinct normalized degree-two Euler coefficient sequences are independent.
This is purely algebraic and uses every prime, including ramified primes. -/
theorem independent (f : I → ℕ → K) (beta : ℕ → K)
    (hf0 : ∀ i, f i 0=0) (hf1 : ∀ i, f i 1=1)
    (hmul : ∀ i m n, m.Coprime n → f i (m*n)=f i m*f i n)
    (hrec : ∀ i p, p.Prime → ∀ j,
      f i (p^(j+2))=f i p*f i (p^(j+1))-beta p*f i (p^j))
    (hinj : Function.Injective f) : LinearIndependent K f := by
  classical
  apply FinitenessEulerIndependence.linearIndependent f beta Nat.Prime hf1
  · intro i p hp n
    exact FinitenessEulerRecurrence.full_recurrence (f i) beta (hf0 i)
      (hmul i) (hrec i) hp n
  · intro i j hij
    by_contra! he
    apply hij
    apply hinj
    exact FinitenessEulerRecurrence.eq_of_prime_eq (f i) (f j) beta
      (hf0 i) (hf0 j) (hf1 i) (hf1 j) (hmul i) (hmul j)
      (hrec i) (hrec j) he

#print axioms independent

end FinitenessEulerFamily
