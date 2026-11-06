module
public import SmallLevelTwentyEightGridWordRowsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightGrid
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open SmallLevelTwentyEightGenerators (E W half_inverse)
open scoped MatrixGroups ModularForm

def gridSourceWord : Fin 10→List (Fin 5×Bool)
  | 0 => [(3,false),(0,false),(4,false)]
  | 1 => [(3,false),(0,false)]
  | 2 => [(3,false),(4,false)]
  | 3 => [(3,false)]
  | 4 => [(3,false),(4,true)]
  | 5 => [(1,false),(3,false)]
  | 6 => [(2,false),(4,true)]
  | 7 => [(1,false),(2,false),(4,true)]
  | 8 => [(2,false),(4,false)]
  | 9 => [(0,true),(0,true),(4,true)]

def gridSourceRaw : Fin 10→Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![0,-1;28,42]
  | 1 => !![0,-1;28,28]
  | 2 => !![0,-1;28,14]
  | 3 => !![0,-1;28,0]
  | 4 => !![0,-1;28,-14]
  | 5 => !![0,-1;28,-28]
  | 6 => !![1,-1;-14,15]
  | 7 => !![1,-1;14,-13]
  | 8 => !![1,0;-14,1]
  | 9 => !![2,-5;0,2]

def gridSourceDet : Fin 10→ℕ
  | 0 => 28
  | 1 => 28
  | 2 => 28
  | 3 => 28
  | 4 => 28
  | 5 => 28
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 4

theorem gridSourceRaw_det (i : Fin 10) : (gridSourceRaw i).det=(gridSourceDet i:ℤ) := by
  fin_cases i <;> norm_num [gridSourceRaw,gridSourceDet,det_fin_two]

theorem gridSourceDet_pos (i : Fin 10) : 0<gridSourceDet i := by
  fin_cases i <;> decide

theorem gridSource_coordinates (i : Fin 10) :
    (gridWord (gridSourceWord i)).val=
      (1/Real.sqrt (gridSourceDet i)) • (gridSourceRaw i).map (Int.castRingHom ℝ) := by
  have hT : (SpecialLinearGroup.mapGL ℝ T)⁻¹=
      SpecialLinearGroup.mapGL ℝ (⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) := by
    rw [← map_inv,show T⁻¹=(⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 28)^2=28 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 28≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases i <;>
    simp only [gridSourceWord,gridWord,gridLetter,gridBase,Bool.false_eq_true,
      ite_false,ite_true,mul_one,hT,←half_inverse]
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [gridSourceRaw,gridSourceDet,W,fricke,E,translation,matrix,
        GeneralLinearGroup.mkOfDetNeZero,T,lower,SpecialLinearGroup.toGL,
        SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Fin.sum_univ_two] <;>
      field_simp [hn] <;> nlinarith

def gridSourceSign (η : ℂ) : Fin 10→ℂ
  | 0 => -η
  | 1 => η
  | 2 => -η
  | 3 => η
  | 4 => -η
  | 5 => η
  | 6 => -1
  | 7 => -1
  | 8 => -1
  | 9 => -1

theorem gridSource_sign (η : ℂ) (i : Fin 10) :
    gridWordSign η (gridSourceWord i)=gridSourceSign η i := by
  fin_cases i <;> simp [gridSourceWord,gridWordSign,gridBaseSign,gridSourceSign]

#print axioms gridSource_coordinates
#print axioms gridSource_sign
end SmallLevelTwentyEightGrid
