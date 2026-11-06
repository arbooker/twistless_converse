module

public import SmallLevelTwentyOneGenerationV1
public import SmallLevelTwentyOneThreeTheoryV4
public import SmallLevelModularCriterionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneGeneration
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open SmallLevelTwentyOneChiFiveGroup SmallLevelTwentyOneThree
open scoped MatrixGroups ModularForm

private theorem conjugate_P_0 :
    SpecialLinearGroup.mapGL ℝ (generator 7)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 0) := by
  rw [show generator 7=(⟨!![22,3;-147,-20],by decide⟩ : SL(2,ℤ)) by decide,show generator 0=(⟨!![1,1;0,1],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_P_1 :
    SpecialLinearGroup.mapGL ℝ (generator 8)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 1) := by
  rw [show generator 8=(⟨!![-41,-7;252,43],by decide⟩ : SL(2,ℤ)) by decide,show generator 1=(⟨!![1,0;21,1],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_P_2 :
    SpecialLinearGroup.mapGL ℝ (generator 9)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 2) := by
  rw [show generator 9=(⟨!![86,13;-483,-73],by decide⟩ : SL(2,ℤ)) by decide,show generator 2=(⟨!![2,-1;-21,11],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_P_3 :
    SpecialLinearGroup.mapGL ℝ (generator 10)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 3) := by
  rw [show generator 10=(⟨!![131,20;-714,-109],by decide⟩ : SL(2,ℤ)) by decide,show generator 3=(⟨!![5,-2;-42,17],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_P_4 :
    SpecialLinearGroup.mapGL ℝ (generator 11)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 4) := by
  rw [show generator 11=(⟨!![47,4;-294,-25],by decide⟩ : SL(2,ℤ)) by decide,show generator 4=(⟨!![5,2;42,17],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_P_5 :
    SpecialLinearGroup.mapGL ℝ (generator 12)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 5) := by
  rw [show generator 12=(⟨!![5,1;-21,-4],by decide⟩ : SL(2,ℤ)) by decide,show generator 5=(⟨!![5,1;-21,-4],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_P_6 :
    SpecialLinearGroup.mapGL ℝ (generator 13)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 6) := by
  rw [show generator 13=(⟨!![-121,-19;777,122],by decide⟩ : SL(2,ℤ)) by decide,show generator 6=(⟨!![5,-1;21,-4],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem conjugate_P (i : Fin 7) :
    SpecialLinearGroup.mapGL ℝ (generator ⟨i.val+7,by omega⟩)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator (i.castLE (by decide))) := by
  fin_cases i
  · exact conjugate_P_0
  · exact conjugate_P_1
  · exact conjugate_P_2
  · exact conjugate_P_3
  · exact conjugate_P_4
  · exact conjugate_P_5
  · exact conjugate_P_6

private theorem conjugate_W_0 :
    SpecialLinearGroup.mapGL ℝ (generator 14)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (generator 0) := by
  rw [show generator 14=(⟨!![1,0;-21,1],by decide⟩ : SL(2,ℤ)) by decide,show generator 0=(⟨!![1,1;0,1],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  field_simp [hn]
  nlinarith

private theorem conjugate_W_1 :
    SpecialLinearGroup.mapGL ℝ (generator 15)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (generator 1) := by
  rw [show generator 15=(⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) by decide,show generator 1=(⟨!![1,0;21,1],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  field_simp [hn]
  nlinarith

private theorem conjugate_W_2 :
    SpecialLinearGroup.mapGL ℝ (generator 16)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (generator 2) := by
  rw [show generator 16=(⟨!![11,1;21,2],by decide⟩ : SL(2,ℤ)) by decide,show generator 2=(⟨!![2,-1;-21,11],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_W_3 :
    SpecialLinearGroup.mapGL ℝ (generator 17)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (generator 3) := by
  rw [show generator 17=(⟨!![17,2;42,5],by decide⟩ : SL(2,ℤ)) by decide,show generator 3=(⟨!![5,-2;-42,17],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_W_4 :
    SpecialLinearGroup.mapGL ℝ (generator 18)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (generator 4) := by
  rw [show generator 18=(⟨!![17,-2;-42,5],by decide⟩ : SL(2,ℤ)) by decide,show generator 4=(⟨!![5,2;42,17],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_W_5 :
    SpecialLinearGroup.mapGL ℝ (generator 19)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (generator 5) := by
  rw [show generator 19=(⟨!![-4,1;-21,5],by decide⟩ : SL(2,ℤ)) by decide,show generator 5=(⟨!![5,1;-21,-4],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_W_6 :
    SpecialLinearGroup.mapGL ℝ (generator 20)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (generator 6) := by
  rw [show generator 20=(⟨!![-4,-1;21,5],by decide⟩ : SL(2,ℤ)) by decide,show generator 6=(⟨!![5,-1;21,-4],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem conjugate_W (i : Fin 7) :
    SpecialLinearGroup.mapGL ℝ (generator ⟨i.val+14,by omega⟩)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (generator (i.castLE (by decide))) := by
  fin_cases i
  · exact conjugate_W_0
  · exact conjugate_W_1
  · exact conjugate_W_2
  · exact conjugate_W_3
  · exact conjugate_W_4
  · exact conjugate_W_5
  · exact conjugate_W_6

private theorem conjugate_PW_0 :
    SpecialLinearGroup.mapGL ℝ (generator 21)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 14) := by
  rw [show generator 21=(⟨!![43,7;-252,-41],by decide⟩ : SL(2,ℤ)) by decide,show generator 14=(⟨!![1,0;-21,1],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_PW_1 :
    SpecialLinearGroup.mapGL ℝ (generator 22)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 15) := by
  rw [show generator 22=(⟨!![-20,-3;147,22],by decide⟩ : SL(2,ℤ)) by decide,show generator 15=(⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_PW_2 :
    SpecialLinearGroup.mapGL ℝ (generator 23)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 16) := by
  rw [show generator 23=(⟨!![-73,-13;483,86],by decide⟩ : SL(2,ℤ)) by decide,show generator 16=(⟨!![11,1;21,2],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_PW_3 :
    SpecialLinearGroup.mapGL ℝ (generator 24)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 17) := by
  rw [show generator 24=(⟨!![-109,-20;714,131],by decide⟩ : SL(2,ℤ)) by decide,show generator 17=(⟨!![17,2;42,5],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_PW_4 :
    SpecialLinearGroup.mapGL ℝ (generator 25)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 18) := by
  rw [show generator 25=(⟨!![-25,-4;294,47],by decide⟩ : SL(2,ℤ)) by decide,show generator 18=(⟨!![17,-2;-42,5],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_PW_5 :
    SpecialLinearGroup.mapGL ℝ (generator 26)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 19) := by
  rw [show generator 26=(⟨!![122,19;-777,-121],by decide⟩ : SL(2,ℤ)) by decide,show generator 19=(⟨!![-4,1;-21,5],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_PW_6 :
    SpecialLinearGroup.mapGL ℝ (generator 27)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator 20) := by
  rw [show generator 27=(⟨!![-4,-1;21,5],by decide⟩ : SL(2,ℤ)) by decide,show generator 20=(⟨!![-4,-1;21,5],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem conjugate_PW (i : Fin 7) :
    SpecialLinearGroup.mapGL ℝ (generator ⟨i.val+21,by omega⟩)*P=
      P*SpecialLinearGroup.mapGL ℝ (generator ⟨i.val+14,by omega⟩) := by
  fin_cases i
  · exact conjugate_PW_0
  · exact conjugate_PW_1
  · exact conjugate_PW_2
  · exact conjugate_PW_3
  · exact conjugate_PW_4
  · exact conjugate_PW_5
  · exact conjugate_PW_6

theorem eigen_conjugate_invariant (F : ℍ → ℂ) (k : ℤ) (g : GL (Fin 2) ℝ)
    (δ : ℂ) (hg : F ∣[k] g=δ • F) (γ κ : SL(2,ℤ))
    (hκ : SpecialLinearGroup.mapGL ℝ κ*g=g*SpecialLinearGroup.mapGL ℝ γ)
    (hγ : F ∣[k] γ=F) : F ∣[k] κ=F := by
  have hh : (F ∣[k] κ) ∣[k] g=F ∣[k] g := by
    change (F ∣[k] SpecialLinearGroup.mapGL ℝ κ) ∣[k] g=F ∣[k] g
    rw [← SlashAction.slash_mul,hκ,SlashAction.slash_mul]
    change (F ∣[k] g) ∣[k] γ=F ∣[k] g
    rw [hg,ModularForm.SL_smul_slash,hγ]
  have h := congrArg (fun G : ℍ → ℂ => G ∣[k] g⁻¹) hh
  simpa only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] using h

theorem all_generators (F : ℍ → ℂ) (k : ℤ) (δ χ : ℂ)
    (hP : F ∣[k] P=δ • F) (hW : F ∣[k] fricke 21 (by decide)=χ • F)
    (hbase : ∀ i : Fin 7, F ∣[k] generator (i.castLE (by decide))=F)
    (i : Fin 28) : F ∣[k] generator i=F := by
  have hWbase (j : Fin 7) : F ∣[k] generator ⟨j.val+14,by omega⟩=F :=
    eigen_conjugate_invariant _ _ _ χ hW _ _ (conjugate_W j) (hbase j)
  by_cases hi : i.val<7
  · exact hbase ⟨i.val,hi⟩
  by_cases hi' : i.val<14
  · have h := eigen_conjugate_invariant _ _ _ δ hP _ _ (conjugate_P ⟨i.val-7,by omega⟩)
      (hbase ⟨i.val-7,by omega⟩)
    convert h using 1; congr 2; apply Fin.ext; simp; omega
  by_cases hi'' : i.val<21
  · have h := hWbase ⟨i.val-14,by omega⟩
    convert h using 1; congr 2; apply Fin.ext; simp; omega
  · have h := eigen_conjugate_invariant _ _ _ δ hP _ _ (conjugate_PW ⟨i.val-21,by omega⟩)
      (hWbase ⟨i.val-21,by omega⟩)
    convert h using 1; congr 2; apply Fin.ext; simp; omega

#print axioms conjugate_P
#print axioms conjugate_W
#print axioms conjugate_PW
#print axioms all_generators
end SmallLevelTwentyOneGeneration
