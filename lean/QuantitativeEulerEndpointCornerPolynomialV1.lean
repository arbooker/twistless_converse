module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCornerPolynomial
open Polynomial

variable {A B : Type*} [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]
    (ρ : A →ₗ[ℝ] B) (hmul : ∀ a b, ρ (a*b)=ρ a*ρ b)

include hmul in
theorem map_pow_corner (a : A) (n : ℕ) : ρ (a^n)=(ρ a)^n*ρ 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ',hmul,ih,←mul_assoc,←pow_succ']

theorem aeval_sum (a : A) (q : ℝ[X]) : aeval a q=∑ i∈q.support, q.coeff i • a^i := by
  rw [aeval_def,eval₂_eq_sum,sum_def]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]

include hmul in
/-- A multiplicative real-linear map need not preserve the global unit.
Its polynomial image uses its own corner projection in every constant term. -/
theorem map_aeval_corner (a : A) (q : ℝ[X]) :
    ρ (aeval a q)=aeval (ρ a) q*ρ 1 := by
  rw [aeval_sum,aeval_sum,map_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,map_pow_corner ρ hmul,smul_mul_assoc]

#print axioms map_pow_corner
#print axioms map_aeval_corner
end QuantitativeEulerEndpointCornerPolynomial
