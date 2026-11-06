module
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
namespace QuantitativeArithmeticTwoColumnKernel

/-- A nonzero common kernel vector forces every two-row minor to vanish. -/
theorem minor_zero {K : Type*} [Field K] (a b c d u v : K)
    (h1 : a*u+b*v=0) (h2 : c*u+d*v=0) (h : u≠0 ∨ v≠0) :
    a*d-b*c=0 := by
  rcases h with hu | hv
  · have hz : (a*d-b*c)*u=0 := by linear_combination d*h1-b*h2
    exact (mul_eq_zero.mp hz).resolve_right hu
  · have hz : (a*d-b*c)*v=0 := by linear_combination a*h2-c*h1
    exact (mul_eq_zero.mp hz).resolve_right hv

#print axioms minor_zero
end QuantitativeArithmeticTwoColumnKernel
