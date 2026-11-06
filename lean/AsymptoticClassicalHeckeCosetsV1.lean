module

public import AsymptoticClassicalHeckeTraceV1
public import AsymptoticAtkinLehnerTraceCosetsV1
public import AsymptoticClassicalTriangularSlashV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix AsymptoticAtkinLehner AsymptoticClassicalCosets
open AsymptoticCongruenceLabels AsymptoticClassicalDiscriminant
open scoped ModularForm MatrixGroups

/-- The fixed level-N matrix in the good-prime double-coset factorization. -/
def heckeSL (N p : ℕ) (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) : SL(2, ℤ) :=
  ⟨!![(p : ℤ), B; -(N : ℤ), A], by simpa [Matrix.det_fin_two, mul_comm] using hAB⟩

theorem heckeSL_mem (N p : ℕ) (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) :
    heckeSL N p A B hAB ∈ CongruenceSubgroup.Gamma0 N := by
  rw [gamma0_mem_dvd]
  exact ⟨-1, by change -(N : ℤ) = (N : ℤ) * -1; ring⟩

/-- Each nonidentity trace summand becomes an upper-triangular Hecke
 representative after a left multiplication in Gamma0(N). -/
theorem dilation_traceSL (N p : ℕ) (hp : 0 < p) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) (a : ℤ) :
    dilationReal p hp * SpecialLinearGroup.mapGL ℝ (traceSL N p A B hAB a) =
      SpecialLinearGroup.mapGL ℝ (heckeSL N p A B hAB) *
        triangularGL 1 a p (by norm_num) (by exact_mod_cast hp) := by
  apply Units.ext
  change (dilationReal p hp).val * (traceSL N p A B hAB a).val.map (fun z : ℤ => (z : ℝ)) =
    (heckeSL N p A B hAB).val.map (fun z : ℤ => (z : ℝ)) *
      (triangularGL 1 a p (by norm_num) (by exact_mod_cast hp)).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dilationReal, AsymptoticCongruenceLabels.dilationGL, GeneralLinearGroup.map,
      GeneralLinearGroup.mkOfDetNeZero, traceSL, heckeSL, triangularGL,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

#print axioms heckeSL_mem
#print axioms dilation_traceSL

end AsymptoticClassicalCusp
