module

public import QuantitativeMaassHighCuspKernelV1
public import AsymptoticCongruenceTransvectionsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels QuantitativeSpectralObservability
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- Integral translation by n in the actual cusp chart A. -/
def cuspParabolicMatrix (A : SL(2,ℤ)) (n : ℤ) : SL(2,ℤ) := A*upperSL n*A⁻¹

theorem cuspParabolicMatrix_bottom_left (A : SL(2,ℤ)) (n : ℤ) :
    cuspParabolicMatrix A n 1 0= -n*(A 1 0)^2 := by
  change (∑ k : Fin 2,(A.val*(upperSL n).val) 1 k*(A⁻¹).val k 0)=_
  rw [SpecialLinearGroup.SL2_inv_expl]
  simp only [Fin.sum_univ_two]
  change (∑ k : Fin 2,A.val 1 k*(upperSL n).val k 0)*A.val 1 1+
    (∑ k : Fin 2,A.val 1 k*(upperSL n).val k 1)*(-A.val 1 0)=_
  simp only [Fin.sum_univ_two]
  change (A.val 1 0*1+A.val 1 1*0)*A.val 1 1+
    (A.val 1 0*n+A.val 1 1*1)*(-A.val 1 0)=_
  ring

/-- Exact divisibility criterion for a parabolic translation in any integral cusp. -/
theorem cuspParabolicMatrix_mem_iff (N : ℕ) (A : SL(2,ℤ)) (n : ℤ) :
    integralLabel (cuspParabolicMatrix A n)∈gamma N ↔ (N:ℤ)∣n*(A 1 0)^2 := by
  rw [QuantitativeSpectralObservability.integralLabel_mem_gamma_iff,gamma0_mem_dvd,cuspParabolicMatrix_bottom_left,
    neg_mul,dvd_neg]

/-- The literal admissible translation parameters are a union of residue
classes modulo N; no cusp-width classification is assumed. -/
theorem cuspParabolicMatrix_mem_add_period_iff (N : ℕ) (A : SL(2,ℤ)) (n k : ℤ) :
    integralLabel (cuspParabolicMatrix A (n+(N:ℤ)*k))∈gamma N ↔
      integralLabel (cuspParabolicMatrix A n)∈gamma N := by
  rw [cuspParabolicMatrix_mem_iff,cuspParabolicMatrix_mem_iff,add_mul]
  have hd : (N:ℤ)∣((N:ℤ)*k)*(A 1 0)^2 := ⟨k*(A 1 0)^2,by ring⟩
  constructor
  · intro h
    simpa only [add_sub_cancel_right] using dvd_sub h hd
  · intro h
    exact dvd_add h hd

#print axioms cuspParabolicMatrix_bottom_left
#print axioms cuspParabolicMatrix_mem_iff
#print axioms cuspParabolicMatrix_mem_add_period_iff

end QuantitativeMaass
