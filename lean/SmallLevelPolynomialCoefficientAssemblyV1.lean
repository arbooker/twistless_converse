module
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelPolynomialCoefficientAssembly
open Polynomial

theorem eq_of_bounded_coefficients {R : Type*} [Semiring R] (p q : Polynomial R)
    (n : ℕ) (hp : p.natDegree<n) (hq : q.natDegree<n)
    (h : ∀ i : Fin n,p.coeff i=q.coeff i) : p=q := by
  ext i
  by_cases hi : i<n
  · exact h ⟨i,hi⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i),
      coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < i)]

theorem coeff_mul_range {R : Type*} [Semiring R] (p q : Polynomial R) (n : ℕ) :
    (p*q).coeff n=∑ i∈Finset.range (n+1),p.coeff i*q.coeff (n-i) := by
  rw [coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i*q.coeff j) n

#print axioms eq_of_bounded_coefficients
#print axioms coeff_mul_range
end SmallLevelPolynomialCoefficientAssembly
