module

public import AsymptoticCongruenceLabelsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceLabels

open Matrix AsymptoticFreshCRT
open scoped MatrixGroups

theorem gamma0_mem_dvd (N : ℕ) (A : SL(2,ℤ)) :
    A∈CongruenceSubgroup.Gamma0 N ↔ (N:ℤ)∣A 1 0 := by
  rw [CongruenceSubgroup.Gamma0_mem,ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem lowerSL_mem (M : ℕ) (j : ℤ) : lowerSL M j∈CongruenceSubgroup.Gamma0 M := by
  rw [gamma0_mem_dvd]
  exact ⟨j,rfl⟩

theorem lowerSL_mul (M : ℕ) (i j : ℤ) : lowerSL M i*lowerSL M j=lowerSL M (i+j) := by
  apply Subtype.ext
  change lower M i*lower M j=lower M (i+j)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [lower,Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem lowerSL_zero (M : ℕ) : lowerSL M 0=1 := by
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;> simp [lowerSL,lower]

theorem lowerSL_inv (M : ℕ) (j : ℤ) : (lowerSL M j)⁻¹=lowerSL M (-j) := by
  apply inv_eq_of_mul_eq_one_left
  rw [lowerSL_mul,neg_add_cancel,lowerSL_zero]

theorem lowerSL_inv_mul_bottom (M : ℕ) (j : ℤ) (A : SL(2,ℤ)) :
    ((lowerSL M j)⁻¹*A) 1 0=A 1 0-(M:ℤ)*j*A 0 0 := by
  rw [lowerSL_inv]
  change ((lowerSL M (-j)).val*A.val) 1 0=_
  simp [lowerSL,lower,Matrix.mul_apply,Fin.sum_univ_two]
  ring

#print axioms gamma0_mem_dvd
#print axioms lowerSL_mem
#print axioms lowerSL_mul
#print axioms lowerSL_zero
#print axioms lowerSL_inv
#print axioms lowerSL_inv_mul_bottom

end AsymptoticCongruenceLabels
