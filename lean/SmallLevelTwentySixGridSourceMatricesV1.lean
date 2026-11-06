module
public import SmallLevelTwentySixGridRawWordsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Matrix

def sourceWord : Fin 27→List (Fin 4×Bool) :=
  ![[(1,false),(0,true)],
    [(1,false),(0,true),(0,true)],
    [(1,false),(1,false),(0,true)],
    [(1,false),(1,false),(2,false)],
    [(1,false),(2,false)],
    [(1,false),(2,false),(0,false)],
    [(1,false),(2,false),(0,true)],
    [(1,true)],
    [(1,true),(0,true)],
    [(1,true),(0,true),(0,true)],
    [(1,true),(1,true),(0,true)],
    [(1,true),(1,true),(1,true)],
    [(1,true),(1,true),(2,false)],
    [(1,true),(2,false)],
    [(2,false)],
    [(2,false),(0,false)],
    [(2,false),(0,false),(0,false)],
    [(2,false),(0,true)],
    [(2,false),(0,true),(0,true)],
    [(2,true),(1,true)],
    [(2,true),(1,true),(2,false)],
    [(3,false)],
    [(3,false),(0,false)],
    [(3,false),(0,false),(0,false)],
    [(3,false),(0,true)],
    [(3,false),(2,false)],
    [(3,false),(2,false),(0,true)]]

def sourceRaw : Fin 27→Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![1,-1;26,-25],
    !![1,-2;26,-51],
    !![1,-1;52,-51],
    !![2,-1;78,-38],
    !![2,-1;26,-12],
    !![2,1;26,14],
    !![2,-3;26,-38],
    !![1,0;-26,1],
    !![1,-1;-26,27],
    !![1,-2;-26,53],
    !![1,-1;-52,53],
    !![1,0;-78,1],
    !![2,-1;-130,66],
    !![2,-1;-78,40],
    !![2,-1;-26,14],
    !![2,1;-26,-12],
    !![2,3;-26,-38],
    !![2,-3;-26,40],
    !![2,-5;-26,66],
    !![12,-1;26,-2],
    !![25,-13;52,-27],
    !![0,1;-26,0],
    !![0,1;-26,-26],
    !![0,1;-26,-52],
    !![0,1;-26,26],
    !![13,-7;26,-13],
    !![13,-20;26,-39]]

def sourceMultiple : Fin 27→ℤ :=
  ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,-1,-2,-1,-1,-1,-1,2,2]

theorem source_primitive (i : Fin 27) :
    rawWord (sourceWord i)=sourceMultiple i • sourceRaw i := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [sourceWord,sourceRaw,sourceMultiple,rawWord,rawLetter,rawBase,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

theorem source_nonaffine (i : Fin 27) : sourceRaw i 1 0≠0 := by
  fin_cases i <;> decide

theorem source_det_pos (i : Fin 27) : 0<(sourceRaw i).det := by
  fin_cases i <;> decide

theorem source_coordinates (i : Fin 27) :
    (gridWord (sourceWord i)).val=
      (wordScale (sourceWord i)*(sourceMultiple i:ℝ)) • (sourceRaw i).map (Int.castRingHom ℝ) :=
  primitive_word_coordinates _ _ _ (source_primitive i)

#print axioms source_primitive
#print axioms source_coordinates

end SmallLevelTwentySixGrid
