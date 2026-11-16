module

public import QuantitativeMaassExactAtkinProductV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticFreshMatrices
open AsymptoticReconstructionBranch
open scoped MatrixGroups

namespace QuantitativeMaass

/-- The exact-divisor-one representative is a congruence transformation. -/
theorem exactAtkin_one_mem (N : ℕ) (A B : ℤ) (hAB : (1:ℤ)*A+(N:ℤ)*B=1) :
    exactAtkinLabel N 1 (by decide) A B hAB∈gamma N := by
  let a : SL(2,ℤ) := ⟨exactAtkinMatrix N 1 A B,exactAtkinMatrix_det N 1 A B hAB⟩
  have ha : a∈CongruenceSubgroup.Gamma0 N := by
    rw [gamma0_mem_dvd]
    exact ⟨-1,by simp [a,exactAtkinMatrix]⟩
  refine ⟨a,ha,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (rationalGL a)=rationalMap (exactAtkinGL N 1 (by decide) A B hAB)
  apply congrArg rationalMap
  apply Units.ext
  rfl

/-- At the full exact divisor, the representative agrees with the
Fricke transformation up to an explicit integral congruence factor. -/
theorem exactAtkin_full_fricke (N : ℕ) (hN : 0<N) (A B : ℤ)
    (hAB : (N:ℤ)*A+(1:ℤ)*B=1) :
    ∃ a : gamma N,exactAtkinLabel 1 N hN A B hAB=a.val*frickeLabel N hN := by
  let a : SL(2,ℤ) := ⟨!![-B,1;-(N:ℤ)*A,-1],by
    rw [Matrix.det_fin_two]
    dsimp
    linear_combination hAB⟩
  have ha : a∈CongruenceSubgroup.Gamma0 N := by
    rw [gamma0_mem_dvd]
    exact ⟨-A,by dsimp [a];ring⟩
  refine ⟨⟨integralLabel a,⟨a,ha,rfl⟩⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (exactAtkinGL 1 N hN A B hAB)=
    rationalMap (rationalGL a)*rationalMap (branch (N:ℚ) 0 0 (by exact_mod_cast hN.ne'))
  rw [←map_mul]
  apply congrArg rationalMap
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exactAtkinGL,exactAtkinMatrix,rationalGL_apply,a,branch,
      GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two]

#print axioms exactAtkin_one_mem
#print axioms exactAtkin_full_fricke

end QuantitativeMaass
