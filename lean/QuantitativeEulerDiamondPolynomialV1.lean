module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondPolynomial

open Polynomial Finset

def geometric (ℓ : ℕ) : ℚ[X] := ∑ j ∈ range ℓ, X^j

/-- The actual averaged nontrivial translation polynomial. -/
def kernel (ℓ : ℕ) : ℚ[X] := geometric ℓ-1

def triangular (ℓ : ℕ) : ℚ[X] := ∑ j ∈ range ℓ, geometric j

def inversePolynomial (ℓ : ℕ) : ℚ[X] :=
  C ((ℓ : ℚ)-1)⁻¹ * (kernel ℓ-C ((ℓ : ℚ)-2))

def correctionPolynomial (ℓ : ℕ) : ℚ[X] := C ((ℓ : ℚ)-1)⁻¹ * triangular ℓ

theorem triangular_identity (ℓ : ℕ) :
    (X-1)*triangular ℓ=geometric ℓ-C (ℓ : ℚ) := by
  unfold triangular
  rw [mul_sum]
  simp only [geometric,mul_geom_sum,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul]
  simp

/-- The cyclic averaging identity, with its explicit polynomial remainder.
It is valid before imposing periodicity. -/
theorem kernel_remainder (ℓ : ℕ) :
    kernel ℓ*(kernel ℓ-C ((ℓ : ℚ)-2))-C ((ℓ : ℚ)-1)=
      (X^ℓ-1)*triangular ℓ := by
  have hg : geometric ℓ*(X-1)=X^ℓ-1 := geom_sum_mul X ℓ
  rw [←hg,mul_assoc,triangular_identity]
  simp only [kernel,map_sub,map_ofNat,map_one]
  ring

/-- Fixed-prime diamond cancellation has an exact finite inverse modulo
the period relation X^ℓ=1. The correction is explicit, not a divisibility
or polynomial-existence assumption. Primality is not needed for this step. -/
theorem inverse_identity (ℓ : ℕ) (hℓ : 2≤ℓ) :
    kernel ℓ*inversePolynomial ℓ-1=(X^ℓ-1)*correctionPolynomial ℓ := by
  have hd : (ℓ : ℚ)-1≠0 := by
    have hl : (2 : ℚ)≤ℓ := by exact_mod_cast hℓ
    linarith
  have hc : C ((ℓ : ℚ)-1)⁻¹ * C ((ℓ : ℚ)-1)=(1 : ℚ[X]) := by
    rw [←map_mul,inv_mul_cancel₀ hd,map_one]
  calc
    _ = C ((ℓ : ℚ)-1)⁻¹ *
        (kernel ℓ*(kernel ℓ-C ((ℓ : ℚ)-2))-C ((ℓ : ℚ)-1)) := by
      rw [mul_sub,hc]
      unfold inversePolynomial
      ring
    _ = _ := by
      rw [kernel_remainder]
      unfold correctionPolynomial
      ring

/-- Evaluation gives the same exact relation for one bounded operator,
one group-algebra translation, or any element of a rational algebra. -/
theorem evaluated_inverse {R : Type*} [Ring R] [Algebra ℚ R]
    (x : R) (ℓ : ℕ) (hℓ : 2≤ℓ) :
    aeval x (kernel ℓ)*aeval x (inversePolynomial ℓ)-1=
      (x^ℓ-1)*aeval x (correctionPolynomial ℓ) := by
  have h := congrArg (aeval x) (inverse_identity ℓ hℓ)
  simpa only [map_sub,map_mul,map_pow,map_one,aeval_X] using h

#print axioms kernel_remainder
#print axioms inverse_identity
#print axioms evaluated_inverse
end QuantitativeEulerDiamondPolynomial
