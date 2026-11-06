module

public import AsymptoticClassicalLocalAtkinMatrixV1
public import AsymptoticClassicalFrickeOperatorV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace AsymptoticClassicalCusp
open UpperHalfPlane Matrix AsymptoticCongruenceLabels
open scoped MatrixGroups

variable (M p : ℕ) (hp : 0 < p) (A B : ℤ) (hAB : (p : ℤ)*A+(M : ℤ)*B=1)

/-- The integral commutator of global and local Atkin--Lehner matrices. -/
def localFrickeCommutator : SL(2, ℤ) :=
  ⟨!![(p : ℤ)*A^2+M, 1-A*B; (p : ℤ)*M*(1-A*B), (M : ℤ)*B^2+p], by
    rw [Matrix.det_fin_two]
    change ((p : ℤ)*A^2+M)*((M : ℤ)*B^2+p) - (1-A*B)*((p : ℤ)*M*(1-A*B)) = 1
    calc
      _ = ((p : ℤ)*A+(M : ℤ)*B)^2 := by ring
      _ = 1 := by rw [hAB]; norm_num⟩

theorem localFrickeCommutator_mem :
    localFrickeCommutator M p A B hAB ∈ CongruenceSubgroup.Gamma0 (p*M) := by
  rw [gamma0_mem_dvd]
  exact ⟨1-A*B, by simp [localFrickeCommutator]⟩

theorem localAtkin_fricke_intertwine (hM : 0 < M) :
    frickeReal (p*M) (Nat.mul_pos hp hM) * localAtkinReal M p hp A B hAB =
      SpecialLinearGroup.mapGL ℝ (localFrickeCommutator M p A B hAB) *
        localAtkinReal M p hp A B hAB * frickeReal (p*M) (Nat.mul_pos hp hM) := by
  have hab : (p : ℝ)*(A : ℝ)+(M : ℝ)*(B : ℝ)=1 := by exact_mod_cast hAB
  have hw : (frickeReal (p*M) (Nat.mul_pos hp hM)).val = !![0,-1;(p : ℝ)*M,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [frickeReal, fricke, AsymptoticReconstructionBranch.branch,
        GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero]
  have hm : (localFrickeCommutator M p A B hAB).val.map (fun z : ℤ => (z : ℝ)) *
      (localAtkinReal M p hp A B hAB).val * (frickeReal (p*M) (Nat.mul_pos hp hM)).val =
      ((p : ℝ)*(A : ℝ)+(M : ℝ)*(B : ℝ)) •
        ((frickeReal (p*M) (Nat.mul_pos hp hM)).val * (localAtkinReal M p hp A B hAB).val) := by
    rw [localAtkinReal_val, hw]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [localFrickeCommutator, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring_nf <;> simp
  rw [hab, one_smul] at hm
  exact Units.ext hm.symm

#print axioms localFrickeCommutator_mem
#print axioms localAtkin_fricke_intertwine
end AsymptoticClassicalCusp
