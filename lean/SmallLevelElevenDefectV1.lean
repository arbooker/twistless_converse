module

public import SmallLevelThreeSlashV1
public import SmallLevelElevenEllipticV1
public import SmallLevelThirtySixOrbitV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelEleven

open Matrix UpperHalfPlane ModularGroup SmallLevelThree SmallLevelGenerators
open scoped MatrixGroups ModularForm

def ellipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ elliptic

theorem sub_slash (g h : ℍ → ℂ) (k : ℤ) (M : GL (Fin 2) ℝ) :
    (g-h) ∣[k] M=(g ∣[k] M)-(h ∣[k] M) := by
  simp only [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash]

theorem positive_branch : lowerBranch 11 1=
    SpecialLinearGroup.mapGL ℝ A*upperBranch (-1) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerBranch, upperBranch, A, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem negative_branch : lowerBranch 11 (-1)=
    SpecialLinearGroup.mapGL ℝ B*upperBranch 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerBranch, upperBranch, B, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem elliptic_branch : ellipticReal*upperBranch (-1)=
    SpecialLinearGroup.mapGL ℝ A⁻¹*upperBranch 1 := by
  have hi : A⁻¹=(⟨!![4,-1;-11,3],by decide⟩ : SL(2,ℤ)) := by decide
  rw [hi]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ellipticReal, elliptic, upperBranch, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem B_action (m : ℕ) (g : ℍ → ℂ)
    (ht : g ∣[((2*m:ℕ):ℤ)] T=g)
    (h2 : g ∣[((2*m:ℕ):ℤ)] oddMatrix 11 6 (by decide)=g) :
    g ∣[((2*m:ℕ):ℤ)] B=g ∣[((2*m:ℕ):ℤ)] A⁻¹ := by
  have hi := congrArg (fun F : ℍ → ℂ =>
    F ∣[((2*m:ℕ):ℤ)] (oddMatrix 11 6 (by decide))⁻¹) h2
  simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at hi
  rw [matrix_relation]
  simp only [SlashAction.slash_mul, SmallLevelThirtySix.slash_neg_one_even, ← hi, ht]

/-- The actual level-eleven transformation defect has the explicit
infinite-order elliptic symmetry; no extra eigenvalue condition is used. -/
theorem original_defect_elliptic (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 11 (2*m) f) :
    ((SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A)-
      SmallLevelOriginal.fourierFunction (2*m) f) ∣[((2*m:ℕ):ℤ)] ellipticReal=
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A)-
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let g := SmallLevelOriginal.fourierFunction (2*m) f
  have he := original_pair_slash (by decide : 0<11) (by decide) hf
  have hb := B_action m g (original_T _ _)
    (original_odd (by decide) (by decide) (by decide) hf)
  rw [positive_branch, negative_branch, SlashAction.slash_mul, SlashAction.slash_mul] at he
  change (g ∣[((2*m:ℕ):ℤ)] upperBranch 1)+(g ∣[((2*m:ℕ):ℤ)] upperBranch (-1))=
    ((g ∣[((2*m:ℕ):ℤ)] A) ∣[((2*m:ℕ):ℤ)] upperBranch (-1))+
      ((g ∣[((2*m:ℕ):ℤ)] B) ∣[((2*m:ℕ):ℤ)] upperBranch 1) at he
  rw [hb] at he
  have hh := congrArg (fun F : ℍ → ℂ => F ∣[((2*m:ℕ):ℤ)] (upperBranch (-1))⁻¹) he
  simp only [SlashAction.add_slash, ← SlashAction.slash_mul, mul_inv_cancel,
    SlashAction.slash_one] at hh
  have hm : ellipticReal=SpecialLinearGroup.mapGL ℝ A⁻¹*upperBranch 1*(upperBranch (-1))⁻¹ := by
    rw [← elliptic_branch, mul_assoc, mul_inv_cancel, mul_one]
  have hAE : SpecialLinearGroup.mapGL ℝ A*ellipticReal=
      upperBranch 1*(upperBranch (-1))⁻¹ := by
    rw [hm, ← mul_assoc, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  change ((g ∣[((2*m:ℕ):ℤ)] A)-g) ∣[((2*m:ℕ):ℤ)] ellipticReal=
    (g ∣[((2*m:ℕ):ℤ)] A)-g
  rw [show (g ∣[((2*m:ℕ):ℤ)] A)=g ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ A from rfl]
  simp only [sub_slash, ← SlashAction.slash_mul]
  rw [hAE, hm, mul_assoc]
  rw [SlashAction.slash_mul _ (SpecialLinearGroup.mapGL ℝ A⁻¹)]
  change (g ∣[((2*m:ℕ):ℤ)] (upperBranch 1*(upperBranch (-1))⁻¹))-
    ((g ∣[((2*m:ℕ):ℤ)] A⁻¹) ∣[((2*m:ℕ):ℤ)] (upperBranch 1*(upperBranch (-1))⁻¹))=
      (g ∣[((2*m:ℕ):ℤ)] A)-g
  linear_combination hh

#print axioms positive_branch
#print axioms negative_branch
#print axioms elliptic_branch
#print axioms original_defect_elliptic

end SmallLevelEleven
