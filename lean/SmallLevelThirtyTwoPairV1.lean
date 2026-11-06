module

public import SmallLevelThreeSlashV1
public import SmallLevelEvenScaleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelThirtyTwo

open Matrix UpperHalfPlane ModularGroup SmallLevelThree SmallLevelGenerators SmallLevelEvenScale
open scoped MatrixGroups ModularForm

def halfPoint (z : ℍ) : ℍ := ⟨(z:ℂ)/2, by simpa using div_pos z.im_pos (by norm_num : (0:ℝ)<2)⟩

theorem half_lower_point (j : ℤ) (z : ℍ) :
    ((lowerBranch 16 j • z : ℍ):ℂ)/2=((lowerBranch 32 j • halfPoint z : ℍ):ℂ) := by
  rw [lowerBranch_point, lowerBranch_point]
  simp only [halfPoint, coe_mk, Nat.cast_ofNat]
  rw [show (j:ℂ)*32*((z:ℂ)/2)+1=j*16*(z:ℂ)+1 by ring]
  ring

theorem scaled_pair {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 32 k f) :
    (scaledFunction k f ∣[(k:ℤ)] upperBranch 2)+(scaledFunction k f ∣[(k:ℤ)] upperBranch (-2))=
    (scaledFunction k f ∣[(k:ℤ)] lowerBranch 16 1)+(scaledFunction k f ∣[(k:ℤ)] lowerBranch 16 (-1)) := by
  funext z
  have hh := original_pair (by decide : 0<32) (by decide) hf (halfPoint z)
  simp only [halfPoint, coe_mk, Nat.cast_ofNat] at hh
  simp only [Pi.add_apply, upperBranch_slash, lowerBranch_slash,
    scaledFunction, scaledFourier, upperBranch_point, half_lower_point,
    Int.cast_ofNat, Int.cast_neg, Int.cast_one, one_mul, neg_one_mul,
    Nat.cast_ofNat]
  rw [show (((z:ℂ)+2)/3)/2=(((z:ℂ)/2)+1)/3 by ring,
    show (((z:ℂ)+ -2)/3)/2=(((z:ℂ)/2)-1)/3 by ring]
  rw [show (32:ℂ)*((z:ℂ)/2)+1=16*(z:ℂ)+1 by ring,
    show -(32:ℂ)*((z:ℂ)/2)+1= -16*(z:ℂ)+1 by ring] at hh
  simp only [halfPoint]
  linear_combination hh/3

theorem branch_upper_pos : upperBranch 2=SpecialLinearGroup.mapGL ℝ T*upperBranch (-1) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperBranch, ModularGroup.T, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem branch_upper_neg : upperBranch (-2)=SpecialLinearGroup.mapGL ℝ T⁻¹*upperBranch 1 := by
  have hi : T⁻¹=(⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) := by decide
  rw [hi]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperBranch, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem branch_lower_pos : lowerBranch 16 1=
    SpecialLinearGroup.mapGL ℝ (lower 8)*lowerBranch 8 (-1) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerBranch, lower, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem branch_lower_neg : lowerBranch 16 (-1)=
    SpecialLinearGroup.mapGL ℝ (lower 8)⁻¹*lowerBranch 8 1 := by
  have hi : (lower 8)⁻¹=(⟨!![1,0;-8,1],by decide⟩ : SL(2,ℤ)) := by decide
  rw [hi]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerBranch, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem anti_inverse (g : ℍ → ℂ) (k : ℤ) (M : SL(2,ℤ))
    (h : g ∣[k] M= -g) : g ∣[k] M⁻¹= -g := by
  have hh := congrArg (fun F : ℍ → ℂ => F ∣[k] M⁻¹) h
  simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
    SlashAction.neg_slash] at hh
  exact neg_eq_iff_eq_neg.mp hh.symm

/-- The two minus-generator laws turn the original modulus-three relation
into the level-eight pair required by the elliptic defect argument. -/
theorem actual_pair {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 32 k f) :
    (scaledFunction k f ∣[(k:ℤ)] upperBranch 1)+(scaledFunction k f ∣[(k:ℤ)] upperBranch (-1))=
    (scaledFunction k f ∣[(k:ℤ)] lowerBranch 8 1)+(scaledFunction k f ∣[(k:ℤ)] lowerBranch 8 (-1)) := by
  have ht := scaled_T (L:=8) hf.toEulerData (k:=k)
  have hu := scaled_lower (by decide : 0<8) hf
  have hti := anti_inverse _ _ _ ht
  have hui := anti_inverse _ _ _ hu
  have hh := scaled_pair hf
  rw [branch_upper_pos, branch_upper_neg, branch_lower_pos, branch_lower_neg] at hh
  simp only [SlashAction.slash_mul] at hh
  change ((scaledFunction k f ∣[(k:ℤ)] T) ∣[(k:ℤ)] upperBranch (-1))+
      ((scaledFunction k f ∣[(k:ℤ)] T⁻¹) ∣[(k:ℤ)] upperBranch 1)=
    ((scaledFunction k f ∣[(k:ℤ)] lower 8) ∣[(k:ℤ)] lowerBranch 8 (-1))+
      ((scaledFunction k f ∣[(k:ℤ)] (lower 8)⁻¹) ∣[(k:ℤ)] lowerBranch 8 1) at hh
  rw [ht, hti, hu, hui] at hh
  simp only [SlashAction.neg_slash] at hh
  linear_combination -hh

#print axioms scaled_pair
#print axioms actual_pair

end SmallLevelThirtyTwo
