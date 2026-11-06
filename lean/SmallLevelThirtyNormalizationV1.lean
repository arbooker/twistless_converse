module

public import SmallLevelThirtyGeneratorDataV1
public import SmallLevelIntegerNormalizationV1
public import SmallLevelThirtyRootsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
@[expose] public noncomputable section

namespace SmallLevelThirty

open Matrix ModularGroup SmallLevelIntegerNormalization SmallLevelNormalized
open scoped MatrixGroups ModularForm

def rawRep : Fin 8 → IntegerMatrix
  | 0 => !![1,0;0,1]
  | 1 => !![16,1;30,2]
  | 2 => !![6,1;30,6]
  | 3 => !![63,11;120,21]
  | 4 => !![0,1;-30,0]
  | 5 => !![15,-8;30,-15]
  | 6 => !![5,-1;30,-5]
  | 7 => !![110,-21;210,-40]

def repDet : Fin 8 → ℕ := ![1,2,6,3,30,15,5,10]

theorem rep_positive : ∀ i : Fin 8, 0<repDet i := by decide

theorem rawRep_det : ∀ i : Fin 8, rawRep i 0 0*rawRep i 1 1-rawRep i 0 1*rawRep i 1 0=(repDet i:ℤ) := by decide

def realRep (i : Fin 8) : GL (Fin 2) ℝ := SmallLevelIntegerNormalization.normalize (rawRep i) (repDet i) (rep_positive i) (rawRep_det i)

theorem realRep_det (i : Fin 8) : (GeneralLinearGroup.det (realRep i):ℝ)=1 := normalize_det _ _ _ _

def rawGen : Fin 5 → IntegerMatrix
  | 0 => !![1,1;0,1]
  | 1 => !![16,1;30,2]
  | 2 => !![6,1;30,6]
  | 3 => !![0,-1;30,0]
  | 4 => !![4,-1;-30,8]

def genDet : Fin 5 → ℕ := ![1,2,6,30,2]

theorem gen_positive : ∀ i : Fin 5, 0<genDet i := by decide

theorem rawGen_det : ∀ i : Fin 5, rawGen i 0 0*rawGen i 1 1-rawGen i 0 1*rawGen i 1 0=(genDet i:ℤ) := by decide

def realGen (i : Fin 5) : GL (Fin 2) ℝ := SmallLevelIntegerNormalization.normalize (rawGen i) (genDet i) (gen_positive i) (rawGen_det i)

theorem realGen_det (i : Fin 5) : (GeneralLinearGroup.det (realGen i):ℝ)=1 := normalize_det _ _ _ _

def kernelAt : Fin 27 → SL(2,ℤ)
  | 0 => generator 0
  | 1 => generator 1
  | 2 => generator 2
  | 3 => generator 3
  | 4 => generator 4
  | 5 => generator 5
  | 6 => generator 6
  | 7 => generator 7
  | 8 => generator 8
  | 9 => generator 9
  | 10 => generator 10
  | 11 => generator 11
  | 12 => generator 12
  | 13 => generator 13
  | 14 => generator 14
  | 15 => generator 15
  | 16 => generator 16
  | 17 => generator 17
  | 18 => generator 18
  | 19 => generator 19
  | 20 => generator 20
  | 21 => generator 21
  | 22 => generator 22
  | 23 => generator 23
  | 24 => generator 24
  | 25 => generator 25
  | _ => 1

def edgeData : Fin 8 → Fin 5 → Fin 8 × Fin 27 × ℤ
  | 0 => ![(0,0,1),(1,26,1),(2,26,1),(4,26,-1),(1,1,1)]
  | 1 => ![(1,2,-1),(0,3,2),(3,26,2),(5,26,2),(0,4,2)]
  | 2 => ![(2,5,-1),(3,6,2),(0,7,6),(6,26,6),(3,8,-2)]
  | 3 => ![(3,9,-1),(2,10,1),(1,11,-3),(7,26,3),(2,12,-1)]
  | 4 => ![(4,13,1),(5,14,-2),(6,15,-6),(0,26,30),(5,16,2)]
  | 5 => ![(5,17,-1),(4,26,-1),(7,18,3),(1,26,-15),(4,19,-1)]
  | 6 => ![(6,20,-1),(7,21,-1),(4,26,-1),(2,26,-5),(7,22,1)]
  | 7 => ![(7,23,-1),(6,24,-2),(5,26,2),(3,26,-10),(6,25,2)]

def nextIndex (r : Fin 8) (j : Fin 5) : Fin 8 := (edgeData r j).1

def edgeScale (r : Fin 8) (j : Fin 5) : ℕ := (edgeData r j).2.2.natAbs

def edgeKernel (r : Fin 8) (j : Fin 5) : SL(2,ℤ) :=
  if 0≤(edgeData r j).2.2 then kernelAt (edgeData r j).2.1
  else (-1)*kernelAt (edgeData r j).2.1

theorem scale_positive : ∀ r j, 0<edgeScale r j := by decide

theorem raw_edge_checked : ∀ r j,
    rawRep r*rawGen j=(edgeScale r j:ℤ) • ((edgeKernel r j:IntegerMatrix)*rawRep (nextIndex r j)) := by decide

theorem determinant_edge_checked : ∀ r j,
    (repDet r:ℤ)*genDet j=(edgeScale r j:ℤ)^2*repDet (nextIndex r j) := by decide

theorem normalized_edge (r : Fin 8) (j : Fin 5) :
    realRep r*realGen j=SpecialLinearGroup.mapGL ℝ (edgeKernel r j)*realRep (nextIndex r j) :=
  normalized_relation _ _ _ _ _ _ _ _ _ _ _ _ (edgeKernel r j) (edgeScale r j)
    (by exact_mod_cast scale_positive r j) (raw_edge_checked r j) (determinant_edge_checked r j)

theorem realRep_zero : realRep 0=1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realRep,SmallLevelIntegerNormalization.normalize,rawRep,repDet,matrix,GeneralLinearGroup.mkOfDetNeZero]

theorem realGen_0 : realGen 0=SpecialLinearGroup.mapGL ℝ T := by
  have hs : (Real.sqrt 30)^2=30 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 30≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realGen,SmallLevelIntegerNormalization.normalize,rawGen,genDet,matrix,GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,ModularGroup.T]

theorem realGen_1 : realGen 1=SmallLevelRamifiedTwo.Q 30 16 (by decide) := by
  have hs : (Real.sqrt 30)^2=30 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 30≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realGen,SmallLevelIntegerNormalization.normalize,rawGen,genDet,matrix,GeneralLinearGroup.mkOfDetNeZero,SmallLevelRamifiedTwo.Q]

theorem realGen_2 : realGen 2=SmallLevelThirtyB.A := by
  have hs : (Real.sqrt 30)^2=30 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 30≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realGen,SmallLevelIntegerNormalization.normalize,rawGen,genDet,matrix,GeneralLinearGroup.mkOfDetNeZero,SmallLevelThirtyB.A]

theorem realGen_3 : realGen 3=fricke 30 (by decide) := by
  have hs : (Real.sqrt 30)^2=30 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 30≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realGen,SmallLevelIntegerNormalization.normalize,rawGen,genDet,matrix,GeneralLinearGroup.mkOfDetNeZero,fricke]

theorem realGen_4 : realGen 4=SmallLevelThirtyC.C := by
  have hs : (Real.sqrt 30)^2=30 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 30≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realGen,SmallLevelIntegerNormalization.normalize,rawGen,genDet,matrix,GeneralLinearGroup.mkOfDetNeZero,SmallLevelThirtyC.C]

theorem generator_covered : ∀ i : Fin 26, ∃ r : Fin 8, ∃ j : Fin 5,
    edgeKernel r j=generator i ∨ edgeKernel r j=(-1)*generator i := by decide

#print axioms raw_edge_checked
#print axioms determinant_edge_checked
#print axioms normalized_edge
#print axioms generator_covered

end SmallLevelThirty
