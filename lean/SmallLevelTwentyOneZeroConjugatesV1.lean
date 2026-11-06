module

public import SmallLevelTwentyOneZeroTheoryV4
public import SmallLevelTwentyOneConjugatesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneZero
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open scoped MatrixGroups ModularForm

def sourceIndex : Fin 12 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 14
  | 8 => 16
  | 9 => 18
  | 10 => 20
  | _ => 22

def partnerIndex : Fin 12 → Fin 24
  | 0 => 7
  | 1 => 8
  | 2 => 9
  | 3 => 10
  | 4 => 11
  | 5 => 12
  | 6 => 13
  | 7 => 15
  | 8 => 17
  | 9 => 19
  | 10 => 21
  | _ => 23

def conjugateMatrix : Fin 12 → SL(2,ℤ)
  | 0 => (⟨!![1,0;-21,1],by decide⟩ : SL(2,ℤ))
  | 1 => (⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ))
  | 2 => (⟨!![11,1;21,2],by decide⟩ : SL(2,ℤ))
  | 3 => (⟨!![17,2;42,5],by decide⟩ : SL(2,ℤ))
  | 4 => (⟨!![17,-2;-42,5],by decide⟩ : SL(2,ℤ))
  | 5 => (⟨!![-41,14;-126,43],by decide⟩ : SL(2,ℤ))
  | 6 => (⟨!![-83,14;-504,85],by decide⟩ : SL(2,ℤ))
  | 7 => (⟨!![421,24;1491,85],by decide⟩ : SL(2,ℤ))
  | 8 => (⟨!![-1555,-64;7119,293],by decide⟩ : SL(2,ℤ))
  | 9 => (⟨!![1133,64;5187,293],by decide⟩ : SL(2,ℤ))
  | 10 => (⟨!![-2645,-104;9639,379],by decide⟩ : SL(2,ℤ))
  | _ => (⟨!![76,5;5943,391],by decide⟩ : SL(2,ℤ))

private theorem conjugate_checked_0 :
    SpecialLinearGroup.mapGL ℝ (conjugateMatrix 0)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel 0) := by
  rw [show conjugateMatrix 0=(⟨!![1,0;-21,1],by decide⟩ : SL(2,ℤ)) by decide,
    show kernel 0=(⟨!![1,1;0,1],by decide⟩ : SL(2,ℤ)) by decide]
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

private theorem conjugate_checked_1 :
    SpecialLinearGroup.mapGL ℝ (conjugateMatrix 1)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel 1) := by
  rw [show conjugateMatrix 1=(⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) by decide,
    show kernel 1=(⟨!![1,0;21,1],by decide⟩ : SL(2,ℤ)) by decide]
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

private theorem conjugate_checked_2 :
    SpecialLinearGroup.mapGL ℝ (conjugateMatrix 2)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel 2) := by
  rw [show conjugateMatrix 2=(⟨!![11,1;21,2],by decide⟩ : SL(2,ℤ)) by decide,
    show kernel 2=(⟨!![2,-1;-21,11],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

private theorem conjugate_checked_3 :
    SpecialLinearGroup.mapGL ℝ (conjugateMatrix 3)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel 3) := by
  rw [show conjugateMatrix 3=(⟨!![17,2;42,5],by decide⟩ : SL(2,ℤ)) by decide,
    show kernel 3=(⟨!![5,-2;-42,17],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

private theorem conjugate_checked_4 :
    SpecialLinearGroup.mapGL ℝ (conjugateMatrix 4)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel 4) := by
  rw [show conjugateMatrix 4=(⟨!![17,-2;-42,5],by decide⟩ : SL(2,ℤ)) by decide,
    show kernel 4=(⟨!![5,2;42,17],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

private theorem conjugate_checked_5 :
    SpecialLinearGroup.mapGL ℝ (conjugateMatrix 5)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel 5) := by
  rw [show conjugateMatrix 5=(⟨!![-41,14;-126,43],by decide⟩ : SL(2,ℤ)) by decide,
    show kernel 5=(⟨!![43,6;-294,-41],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

private theorem conjugate_checked_6 :
    SpecialLinearGroup.mapGL ℝ (conjugateMatrix 6)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel 6) := by
  rw [show conjugateMatrix 6=(⟨!![-83,14;-504,85],by decide⟩ : SL(2,ℤ)) by decide,
    show kernel 6=(⟨!![85,24;-294,-83],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

private theorem conjugate_checked_7 :
    SpecialLinearGroup.mapGL ℝ (conjugateMatrix 7)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel 14) := by
  rw [show conjugateMatrix 7=(⟨!![421,24;1491,85],by decide⟩ : SL(2,ℤ)) by decide,
    show kernel 14=(⟨!![85,-71;-504,421],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

private theorem conjugate_checked_8 :
    SpecialLinearGroup.mapGL ℝ (conjugateMatrix 8)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel 16) := by
  rw [show conjugateMatrix 8=(⟨!![-1555,-64;7119,293],by decide⟩ : SL(2,ℤ)) by decide,
    show kernel 16=(⟨!![293,-339;1344,-1555],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

private theorem conjugate_checked_9 :
    SpecialLinearGroup.mapGL ℝ (conjugateMatrix 9)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel 18) := by
  rw [show conjugateMatrix 9=(⟨!![1133,64;5187,293],by decide⟩ : SL(2,ℤ)) by decide,
    show kernel 18=(⟨!![293,-247;-1344,1133],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

private theorem conjugate_checked_10 :
    SpecialLinearGroup.mapGL ℝ (conjugateMatrix 10)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel 20) := by
  rw [show conjugateMatrix 10=(⟨!![-2645,-104;9639,379],by decide⟩ : SL(2,ℤ)) by decide,
    show kernel 20=(⟨!![379,-459;2184,-2645],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

private theorem conjugate_checked_11 :
    SpecialLinearGroup.mapGL ℝ (conjugateMatrix 11)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel 22) := by
  rw [show conjugateMatrix 11=(⟨!![76,5;5943,391],by decide⟩ : SL(2,ℤ)) by decide,
    show kernel 22=(⟨!![391,-283;-105,76],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

theorem conjugate_checked (i : Fin 12) :
    SpecialLinearGroup.mapGL ℝ (conjugateMatrix i)*fricke 21 (by decide)=
      fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel (sourceIndex i)) := by
  fin_cases i
  · exact conjugate_checked_0
  · exact conjugate_checked_1
  · exact conjugate_checked_2
  · exact conjugate_checked_3
  · exact conjugate_checked_4
  · exact conjugate_checked_5
  · exact conjugate_checked_6
  · exact conjugate_checked_7
  · exact conjugate_checked_8
  · exact conjugate_checked_9
  · exact conjugate_checked_10
  · exact conjugate_checked_11

theorem partner_invariant (F : ℍ → ℂ) (k : ℤ) (χ : ℂ)
    (hW : F ∣[k] fricke 21 (by decide)=χ • F)
    (hz : F ∣[k] (-1:SL(2,ℤ))=F) (i : Fin 12)
    (hi : F ∣[k] kernel (sourceIndex i)=F) : F ∣[k] kernel (partnerIndex i)=F := by
  let K := slashStabilizer k F
  have hc : F ∣[k] conjugateMatrix i=F :=
    SmallLevelTwentyOneGeneration.eigen_conjugate_invariant _ _ _ χ hW _ _ (conjugate_checked i) hi
  have hr : ∀ i : Fin 12, kernel (partnerIndex i)=conjugateMatrix i ∨
      kernel (partnerIndex i)=(-1)*conjugateMatrix i := by decide
  rcases hr i with h|h
  · rw [h]; exact hc
  · rw [h]; exact K.mul_mem hz hc

#print axioms conjugate_checked
#print axioms partner_invariant
end SmallLevelTwentyOneZero
