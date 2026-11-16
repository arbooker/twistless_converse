module

public import Mathlib.Tactic.NoncommRing
public import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace QuantitativeArithmeticTwoInvolutionPolynomial

/-- The sum of the two generating involutions of a group of order six
has spectrum among -2,-1,1,2 in every representation. This is an exact
ring identity and does not assume a spectral gap. -/
theorem cube_product {R : Type*} [Ring R] (U V : R)
    (hU : U * U = 1) (hV : V * V = 1) (hUV : (U * V)^3 = 1) :
    (U+V)^4-5*(U+V)^2+4 = 0 := by
  have hUU (x : R) : U*(U*x)=x := by rw [←mul_assoc,hU,one_mul]
  have hVV (x : R) : V*(V*x)=x := by rw [←mul_assoc,hV,one_mul]
  have hfour := congrArg (fun x => V*(U*x)) hUV
  simp only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc,hUU,hVV] at hfour
  have hfour' := congrArg (fun x => U*(x*U)) hfour
  simp only [mul_assoc,hUU,hU,mul_one] at hfour'
  noncomm_ring [hUU,hVV,hU,hV,hfour,hfour']; simp

/-- The order-four alternative gives eigenvalues -2,0,2 for the sum. -/
theorem square_product {R : Type*} [Ring R] (U V : R)
    (hU : U * U = 1) (hV : V * V = 1) (hUV : (U * V)^2 = 1) :
    (U+V)^4-4*(U+V)^2 = 0 := by
  have hUU (x : R) : U*(U*x)=x := by rw [←mul_assoc,hU,one_mul]
  have hVV (x : R) : V*(V*x)=x := by rw [←mul_assoc,hV,one_mul]
  have hfour : U*(V*(U*V))=1 := by simpa only [pow_two,mul_assoc] using hUV
  have hfour' := congrArg (fun x => V*(x*V)) hfour
  simp only [mul_assoc,hV,mul_one,one_mul] at hfour'
  noncomm_ring [hUU,hVV,hU,hV,hfour,hfour']

/-- Reflection in the range of an idempotent is an involution. -/
theorem reflection_square {R : Type*} [Ring R] (P : R) (hP : P*P=P) :
    (2*P-1)*(2*P-1)=1 := by
  simp only [two_mul]
  noncomm_ring [hP]

#print axioms cube_product
#print axioms square_product
#print axioms reflection_square

end QuantitativeArithmeticTwoInvolutionPolynomial
