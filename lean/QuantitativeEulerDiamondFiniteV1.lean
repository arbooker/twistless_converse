module

public import QuantitativeEulerDiamondDefectV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondPolynomial

open Polynomial Finset
variable {R : Type*} [Ring R] [Algebra ℚ R]

theorem kernel_eval_succ (x : R) (n : ℕ) :
    aeval x (kernel (n+1))=∑ i : Fin n, x^(i.val+1) := by
  simp only [kernel,geometric,map_sum,map_pow,aeval_X,
    Finset.sum_range_succ',pow_zero,add_sub_cancel_right]
  exact (Fin.sum_univ_eq_sum_range (fun i => x^(i+1)) n).symm

def finiteAverage (x w : R) {n : ℕ} (branches : Fin n → R) : R :=
  ∑ i, (w*branches i-1)*x^(i.val+1)

def finiteCorrection (x w g gInv : R) {n : ℕ} (branches : Fin n → R) : R :=
  ∑ i, w*(branches i*gInv-1)*g*x^(i.val+1)

theorem finiteAverage_sub_correction (x w g gInv : R) (hig : gInv*g=1)
    {n : ℕ} (branches : Fin n → R) :
    finiteAverage x w branches-finiteCorrection x w g gInv branches=
      (w*g-1)*aeval x (kernel (n+1)) := by
  rw [kernel_eval_succ,mul_sum]
  unfold finiteAverage finiteCorrection
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_sub,sub_mul,mul_assoc,hig,mul_one,one_mul]
  noncomm_ring

/-- Exact inverse using precisely the nonzero finite residue family,
with no auxiliary zeroth branch. -/
theorem finite_diamond_recovery (x w g gInv : R) (hig : gInv*g=1)
    {n : ℕ} (hn : 1≤n) (branches : Fin n → R) :
    w*g-1=
      finiteAverage x w branches*aeval x (inversePolynomial (n+1))-
      finiteCorrection x w g gInv branches*aeval x (inversePolynomial (n+1))-
      (w*g-1)*(x^(n+1)-1)*aeval x (correctionPolynomial (n+1)) := by
  rw [←sub_mul,finiteAverage_sub_correction x w g gInv hig]
  have hi := evaluated_inverse x (n+1) (by omega)
  have hd := congrArg (fun z : R => (w*g-1)*z) hi
  simp only [mul_sub,mul_one] at hd
  rw [mul_assoc,mul_assoc,←hd]
  abel

theorem periodic_finite_recovery {E : Type*} [AddCommGroup E]
    (x w g gInv : R) (hig : gInv*g=1) {n : ℕ} (hn : 1≤n)
    (branches : Fin n → R) (F : R →+ E)
    (hperiod : ∀ A : R, F ((x^(n+1)-1)*A)=0) :
    F (w*g-1)=
      F (finiteAverage x w branches*aeval x (inversePolynomial (n+1)))-
      F (finiteCorrection x w g gInv branches*aeval x (inversePolynomial (n+1)))-
      F (w*(g*x^(n+1)*gInv-1)*g*aeval x (correctionPolynomial (n+1))) := by
  have h := congrArg F (finite_diamond_recovery x w g gInv hig hn branches)
  rw [period_defect x w g gInv hig,sub_mul] at h
  simpa only [map_sub,hperiod,sub_zero] using h

#print axioms kernel_eval_succ
#print axioms finite_diamond_recovery
#print axioms periodic_finite_recovery
end QuantitativeEulerDiamondPolynomial
