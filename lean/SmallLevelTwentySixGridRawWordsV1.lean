module
public import SmallLevelTwentySixGridRawTaylorV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open SmallLevelTwentySixTwelfth (E W)
open scoped MatrixGroups

def rawBase : Fin 4→Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![1,1;0,1]
  | 1 => !![1,0;26,1]
  | 2 => !![2,-1;-26,14]
  | 3 => !![0,-1;26,0]

def rawScale : Fin 4→ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1/Real.sqrt 2
  | 3 => 1/Real.sqrt 26

def rawLetter (i : Fin 4×Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  if i.2 then (rawBase i.1).adjugate else rawBase i.1

def rawWord : List (Fin 4×Bool)→Matrix (Fin 2) (Fin 2) ℤ
  | [] => 1
  | i::w => rawLetter i*rawWord w

def wordScale : List (Fin 4×Bool)→ℝ
  | [] => 1
  | i::w => rawScale i.1*wordScale w

theorem rawBase_coordinates (i : Fin 4) :
    (gridBase i).val=rawScale i • (rawBase i).map (Int.castRingHom ℝ) := by
  have h2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have h26 : (Real.sqrt 26)^2=26 := Real.sq_sqrt (by norm_num)
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn26 : Real.sqrt 26≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [gridBase,rawBase,rawScale,E,W,fricke,matrix,
      GeneralLinearGroup.mkOfDetNeZero,T,lower,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe] <;>
    field_simp [hn2,hn26] <;> norm_num [h2,h26]

private theorem inverse_det_one (g : GL (Fin 2) ℝ)
    (hg : (GeneralLinearGroup.det g:ℝ)=1) :
    (g⁻¹).val=g.val.adjugate := by
  change g.val.det=1 at hg
  rw [GeneralLinearGroup.coe_inv,Matrix.inv_def,hg]
  simp

theorem rawLetter_coordinates (i : Fin 4×Bool) :
    (gridLetter i).val=rawScale i.1 • (rawLetter i).map (Int.castRingHom ℝ) := by
  rcases i with ⟨i,b⟩
  cases b with
  | false => simpa only [gridLetter,rawLetter,Bool.false_eq_true,ite_false] using rawBase_coordinates i
  | true =>
    simp only [gridLetter,rawLetter,ite_true]
    rw [inverse_det_one _ (gridBase_det i),rawBase_coordinates,Matrix.adjugate_smul]
    norm_num only [Fintype.card_fin,Nat.reduceSub,pow_one]
    congr 1
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.adjugate_fin_two,Matrix.map_apply]

/-- Exact integer products account for every word used in the grid.
No numerical matrix normalization or external certificate is trusted. -/
theorem rawWord_coordinates (w : List (Fin 4×Bool)) :
    (gridWord w).val=wordScale w • (rawWord w).map (Int.castRingHom ℝ) := by
  induction w with
  | nil => simp [gridWord,wordScale,rawWord]
  | cons i w ih =>
    simp only [gridWord,wordScale,rawWord,Units.val_mul,rawLetter_coordinates,ih]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.map_apply] <;> ring

/-- A finite integer identity suffices to certify a primitive matrix row. -/
theorem primitive_word_coordinates (w : List (Fin 4×Bool))
    (G : Matrix (Fin 2) (Fin 2) ℤ) (d : ℤ) (hd : rawWord w=d • G) :
    (gridWord w).val=(wordScale w*(d:ℝ)) • G.map (Int.castRingHom ℝ) := by
  rw [rawWord_coordinates,hd]
  ext a b
  simp only [Matrix.smul_apply,Matrix.map_apply,Int.coe_castRingHom,smul_eq_mul,Int.cast_mul]
  ring

#print axioms rawWord_coordinates
#print axioms primitive_word_coordinates
end SmallLevelTwentySixGrid
