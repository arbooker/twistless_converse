module

public import QuantitativeEulerDiamondPolynomialV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondPolynomial

open Polynomial Finset

variable {R : Type*} [Ring R] [Algebra ℚ R]

/-- The sum over the nonzero translation indices. Writing it as a range
sum minus its zeroth summand avoids any choice of finite-index encoding. -/
def averagedResidual (x w : R) (branches : ℕ → R) (ℓ : ℕ) : R :=
  (∑ j ∈ range ℓ, (w*branches j-1)*x^j)-(w*branches 0-1)

/-- The same finite sum of same-residue congruence defects. -/
def congruenceCorrection (x w g gInv : R) (branches : ℕ → R) (ℓ : ℕ) : R :=
  (∑ j ∈ range ℓ, (w*(branches j*gInv-1)*g)*x^j)-
    w*(branches 0*gInv-1)*g

theorem averagedResidual_sub_correction (x w g gInv : R) (hig : gInv*g=1)
    (branches : ℕ → R) (ℓ : ℕ) :
    averagedResidual x w branches ℓ-congruenceCorrection x w g gInv branches ℓ=
      (w*g-1)*aeval x (kernel ℓ) := by
  have he (j : ℕ) :
      (w*branches j-1)*x^j-(w*(branches j*gInv-1)*g)*x^j=(w*g-1)*x^j := by
    simp only [mul_sub,sub_mul,mul_assoc,hig,mul_one,one_mul]
    noncomm_ring
  have hsum := Finset.sum_congr (s₁ := range ℓ) rfl (fun j _ => he j)
  rw [Finset.sum_sub_distrib] at hsum
  have hzero := he 0
  simp only [pow_zero,mul_one] at hzero
  have hk : aeval x (kernel ℓ)=(∑ j ∈ range ℓ, x^j)-1 := by
    simp [kernel,geometric,map_sum]
  rw [hk,mul_sub,mul_one,mul_sum]
  unfold averagedResidual congruenceCorrection
  rw [←hsum,←hzero]
  abel

/-- Exact recovery before evaluating in a right representation. This is
the diamond averaging identity, including its explicit period correction. -/
theorem diamond_recovery (x w g gInv : R) (hig : gInv*g=1)
    (branches : ℕ → R) (ℓ : ℕ) (hℓ : 2≤ℓ) :
    w*g-1=
      averagedResidual x w branches ℓ*aeval x (inversePolynomial ℓ)-
      congruenceCorrection x w g gInv branches ℓ*aeval x (inversePolynomial ℓ)-
      (w*g-1)*(x^ℓ-1)*aeval x (correctionPolynomial ℓ) := by
  rw [←sub_mul,averagedResidual_sub_correction x w g gInv hig]
  have hi := evaluated_inverse x ℓ hℓ
  have hd := congrArg (fun z : R => (w*g-1)*z) hi
  simp only [mul_sub,mul_one] at hd
  rw [mul_assoc,mul_assoc,←hd]
  abel

omit [Algebra ℚ R] in
/-- The correction involves only the conjugate of the period generator
and the period itself. For periodic functions the latter vanishes after
every right translation. -/
theorem period_defect (x w g gInv : R) (hig : gInv*g=1) (ℓ : ℕ) :
    (w*g-1)*(x^ℓ-1)=w*(g*x^ℓ*gInv-1)*g-(x^ℓ-1) := by
  simp only [mul_sub,sub_mul,mul_assoc,hig,mul_one,one_mul]
  noncomm_ring

variable {E : Type*} [AddCommGroup E]

/-- The exact averaged-residual formula for every periodic evaluation.
No congruence invariance or Fricke equation is assumed. -/
theorem periodic_diamond_recovery (x w g gInv : R) (hig : gInv*g=1)
    (branches : ℕ → R) (ℓ : ℕ) (hℓ : 2≤ℓ) (F : R →+ E)
    (hperiod : ∀ A : R, F ((x^ℓ-1)*A)=0) :
    F (w*g-1)=
      F (averagedResidual x w branches ℓ*aeval x (inversePolynomial ℓ))-
      F (congruenceCorrection x w g gInv branches ℓ*aeval x (inversePolynomial ℓ))-
      F (w*(g*x^ℓ*gInv-1)*g*aeval x (correctionPolynomial ℓ)) := by
  have h := congrArg F (diamond_recovery x w g gInv hig branches ℓ hℓ)
  rw [period_defect x w g gInv hig,sub_mul] at h
  simpa only [map_sub,hperiod,sub_zero] using h

omit [Algebra ℚ R] in
/-- Removing the Fricke residual converts the recovered individual
defect into the actual canonical-matrix defect. -/
theorem fricke_canonical_recovery (W w g gInv : R) (hgi : g*gInv=1) (hw : w*w=1) :
    W*gInv-1=((W-w)-w*(w*g-1))*gInv := by
  simp only [mul_sub,sub_mul,mul_one,←mul_assoc,hw,one_mul,hgi]
  noncomm_ring

#print axioms averagedResidual_sub_correction
#print axioms diamond_recovery
#print axioms periodic_diamond_recovery
#print axioms fricke_canonical_recovery
end QuantitativeEulerDiamondPolynomial
