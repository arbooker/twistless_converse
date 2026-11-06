module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import QuantitativeArithmeticSmallLevelNineteenGridAnalyticTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenGridExceptionalCentersV1
public import QuantitativeArithmeticSmallLevelNineteenGridRamanujanRowsV1
public import QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelNineteenGridSystem. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelNineteenGridSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenGridSystem
open Complex Matrix SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelNineteenGridAnalytic
open QuantitativeArithmeticSmallLevelNineteenGridRamanujan

inductive RowKind where
  | group : Fin 45 → RowKind
  | taylor : Fin 18 → RowKind
  | entire : Fin 4 → RowKind
  | center : Fin 3 → RowKind
  | hecke : Fin 47 → RowKind
  deriving DecidableEq

def rowKind0 : Fin 114 → RowKind :=
  ![.group 0,.group 1,.group 2,.group 3,.group 4,.group 5,.group 6,.group 7,.group 8,.group 9,.group 10,.group 11,.group 12,.group 13,.center 0,.group 14,.group 15,.group 16,.group 17,.group 18,.group 19,.group 20,.group 21,.group 22,.group 23,.center 1,.group 24,.group 25,.group 26,.group 27,.group 28,.group 29,.group 30,.group 31,.group 32,.group 33,.group 34,.group 35,.group 36,.group 37,.center 2,.group 38,.group 39,.group 40,.group 41,.group 42,.group 43,.group 44,.entire 0,.taylor 0,.taylor 1,.taylor 2,.taylor 3,.taylor 4,.entire 1,.taylor 5,.taylor 6,.taylor 7,.taylor 8,.taylor 9,.taylor 10,.entire 2,.taylor 11,.taylor 12,.entire 3,.taylor 13,.taylor 14,.taylor 15,.taylor 16,.taylor 17,.hecke 0,.hecke 1,.hecke 2,.hecke 3,.hecke 4,.hecke 5,.hecke 6,.hecke 7,.hecke 8,.hecke 9,.hecke 10,.hecke 11,.hecke 12,.hecke 13,.hecke 14,.hecke 15,.hecke 16,.hecke 17,.hecke 18,.hecke 19,.hecke 20,.hecke 21,.hecke 22,.hecke 23,.hecke 24,.hecke 25,.hecke 26,.hecke 27,.hecke 28,.hecke 29,.hecke 30,.hecke 31,.hecke 32,.hecke 33,.hecke 34,.hecke 35,.hecke 36,.hecke 37,.hecke 38,.hecke 39,.hecke 40,.hecke 41,.hecke 42,.hecke 43]
def rowKind1 : Fin 114 → RowKind :=
  ![.group 0,.group 1,.group 2,.group 3,.group 4,.group 5,.group 6,.group 7,.group 8,.group 9,.group 10,.group 11,.group 12,.group 13,.center 0,.group 14,.group 15,.group 16,.group 17,.group 18,.group 19,.group 20,.group 21,.group 22,.group 23,.center 1,.group 24,.group 25,.group 26,.group 27,.group 28,.group 29,.group 30,.group 31,.group 32,.group 33,.group 34,.group 35,.group 36,.group 37,.center 2,.group 38,.group 39,.group 40,.group 41,.group 42,.group 43,.group 44,.entire 0,.taylor 0,.taylor 1,.taylor 2,.taylor 3,.taylor 4,.entire 1,.taylor 5,.taylor 6,.taylor 7,.taylor 8,.taylor 9,.taylor 10,.entire 2,.taylor 11,.taylor 12,.entire 3,.taylor 13,.taylor 14,.taylor 15,.taylor 16,.taylor 17,.hecke 0,.hecke 1,.hecke 2,.hecke 3,.hecke 4,.hecke 5,.hecke 6,.hecke 7,.hecke 8,.hecke 9,.hecke 10,.hecke 11,.hecke 12,.hecke 13,.hecke 14,.hecke 15,.hecke 16,.hecke 17,.hecke 18,.hecke 19,.hecke 20,.hecke 21,.hecke 22,.hecke 23,.hecke 24,.hecke 25,.hecke 44,.hecke 27,.hecke 28,.hecke 29,.hecke 30,.hecke 31,.hecke 32,.hecke 33,.hecke 34,.hecke 35,.hecke 36,.hecke 37,.hecke 38,.hecke 39,.hecke 40,.hecke 42,.hecke 45,.hecke 46]
def rowKind2 : Fin 114 → RowKind :=
  ![.group 0,.group 1,.group 2,.group 3,.group 4,.group 5,.group 6,.group 7,.group 8,.group 9,.group 10,.group 11,.group 12,.group 13,.center 0,.group 14,.group 15,.group 16,.group 17,.group 18,.group 19,.group 20,.group 21,.group 22,.group 23,.center 1,.group 24,.group 25,.group 26,.group 27,.group 28,.group 29,.group 30,.group 31,.group 32,.group 33,.group 34,.group 35,.group 36,.group 37,.center 2,.group 38,.group 39,.group 40,.group 41,.group 42,.group 43,.group 44,.entire 0,.taylor 0,.taylor 1,.taylor 2,.taylor 3,.taylor 4,.entire 1,.taylor 5,.taylor 6,.taylor 7,.taylor 8,.taylor 9,.taylor 10,.entire 2,.taylor 11,.taylor 12,.entire 3,.taylor 13,.taylor 14,.taylor 15,.taylor 16,.taylor 17,.hecke 0,.hecke 1,.hecke 2,.hecke 3,.hecke 4,.hecke 5,.hecke 6,.hecke 7,.hecke 8,.hecke 9,.hecke 10,.hecke 11,.hecke 12,.hecke 13,.hecke 14,.hecke 15,.hecke 16,.hecke 17,.hecke 18,.hecke 19,.hecke 20,.hecke 21,.hecke 22,.hecke 23,.hecke 24,.hecke 25,.hecke 26,.hecke 27,.hecke 28,.hecke 29,.hecke 30,.hecke 31,.hecke 32,.hecke 33,.hecke 34,.hecke 35,.hecke 36,.hecke 37,.hecke 38,.hecke 39,.hecke 40,.hecke 41,.hecke 42,.hecke 43]
def rowKind3 : Fin 114 → RowKind :=
  ![.group 0,.group 1,.group 2,.group 3,.group 4,.group 5,.group 6,.group 7,.group 8,.group 9,.group 10,.group 11,.group 12,.group 13,.center 0,.group 14,.group 15,.group 16,.group 17,.group 18,.group 19,.group 20,.group 21,.group 22,.group 23,.center 1,.group 24,.group 25,.group 26,.group 27,.group 28,.group 29,.group 30,.group 31,.group 32,.group 33,.group 34,.group 35,.group 36,.group 37,.center 2,.group 38,.group 39,.group 40,.group 41,.group 42,.group 43,.group 44,.entire 0,.taylor 0,.taylor 1,.taylor 2,.taylor 3,.taylor 4,.entire 1,.taylor 5,.taylor 6,.taylor 7,.taylor 8,.taylor 9,.taylor 10,.entire 2,.taylor 11,.taylor 12,.entire 3,.taylor 13,.taylor 14,.taylor 15,.taylor 16,.taylor 17,.hecke 0,.hecke 1,.hecke 2,.hecke 3,.hecke 4,.hecke 5,.hecke 6,.hecke 7,.hecke 8,.hecke 9,.hecke 10,.hecke 11,.hecke 12,.hecke 13,.hecke 14,.hecke 15,.hecke 16,.hecke 17,.hecke 18,.hecke 19,.hecke 20,.hecke 21,.hecke 22,.hecke 23,.hecke 24,.hecke 25,.hecke 44,.hecke 27,.hecke 28,.hecke 29,.hecke 30,.hecke 31,.hecke 32,.hecke 33,.hecke 34,.hecke 35,.hecke 36,.hecke 37,.hecke 38,.hecke 39,.hecke 40,.hecke 42,.hecke 45,.hecke 46]
def rowKind4 : Fin 114 → RowKind :=
  ![.group 0,.group 1,.group 2,.group 3,.group 4,.group 5,.group 6,.group 7,.group 8,.group 9,.group 10,.group 11,.group 12,.group 13,.center 0,.group 14,.group 15,.group 16,.group 17,.group 18,.group 19,.group 20,.group 21,.group 22,.group 23,.center 1,.group 24,.group 25,.group 26,.group 27,.group 28,.group 29,.group 30,.group 31,.group 32,.group 33,.group 34,.group 35,.group 36,.group 37,.center 2,.group 38,.group 39,.group 40,.group 41,.group 42,.group 43,.group 44,.entire 0,.taylor 0,.taylor 1,.taylor 2,.taylor 3,.taylor 4,.entire 1,.taylor 5,.taylor 6,.taylor 7,.taylor 8,.taylor 9,.taylor 10,.entire 2,.taylor 11,.taylor 12,.entire 3,.taylor 13,.taylor 14,.taylor 15,.taylor 16,.taylor 17,.hecke 0,.hecke 1,.hecke 2,.hecke 3,.hecke 4,.hecke 5,.hecke 6,.hecke 7,.hecke 8,.hecke 9,.hecke 10,.hecke 11,.hecke 12,.hecke 13,.hecke 14,.hecke 15,.hecke 16,.hecke 17,.hecke 18,.hecke 19,.hecke 20,.hecke 21,.hecke 22,.hecke 23,.hecke 24,.hecke 25,.hecke 26,.hecke 27,.hecke 28,.hecke 29,.hecke 30,.hecke 31,.hecke 32,.hecke 33,.hecke 34,.hecke 35,.hecke 36,.hecke 37,.hecke 38,.hecke 39,.hecke 40,.hecke 41,.hecke 42,.hecke 43]
def rowKind5 : Fin 114 → RowKind :=
  ![.group 0,.group 1,.group 2,.group 3,.group 4,.group 5,.group 6,.group 7,.group 8,.group 9,.group 10,.group 11,.group 12,.group 13,.center 0,.group 14,.group 15,.group 16,.group 17,.group 18,.group 19,.group 20,.group 21,.group 22,.group 23,.center 1,.group 24,.group 25,.group 26,.group 27,.group 28,.group 29,.group 30,.group 31,.group 32,.group 33,.group 34,.group 35,.group 36,.group 37,.center 2,.group 38,.group 39,.group 40,.group 41,.group 42,.group 43,.group 44,.entire 0,.taylor 0,.taylor 1,.taylor 2,.taylor 3,.taylor 4,.entire 1,.taylor 5,.taylor 6,.taylor 7,.taylor 8,.taylor 9,.taylor 10,.entire 2,.taylor 11,.taylor 12,.entire 3,.taylor 13,.taylor 14,.taylor 15,.taylor 16,.taylor 17,.hecke 0,.hecke 1,.hecke 2,.hecke 3,.hecke 4,.hecke 5,.hecke 6,.hecke 7,.hecke 8,.hecke 9,.hecke 10,.hecke 11,.hecke 12,.hecke 13,.hecke 14,.hecke 15,.hecke 16,.hecke 17,.hecke 18,.hecke 19,.hecke 20,.hecke 21,.hecke 22,.hecke 23,.hecke 24,.hecke 25,.hecke 44,.hecke 27,.hecke 28,.hecke 29,.hecke 30,.hecke 31,.hecke 32,.hecke 33,.hecke 34,.hecke 35,.hecke 36,.hecke 37,.hecke 38,.hecke 39,.hecke 40,.hecke 42,.hecke 45,.hecke 46]
def rowKind6 : Fin 114 → RowKind :=
  ![.group 0,.group 1,.group 2,.group 3,.group 4,.group 5,.group 6,.group 7,.group 8,.group 9,.group 10,.group 11,.group 12,.group 13,.center 0,.group 14,.group 15,.group 16,.group 17,.group 18,.group 19,.group 20,.group 21,.group 22,.group 23,.center 1,.group 24,.group 25,.group 26,.group 27,.group 28,.group 29,.group 30,.group 31,.group 32,.group 33,.group 34,.group 35,.group 36,.group 37,.center 2,.group 38,.group 39,.group 40,.group 41,.group 42,.group 43,.group 44,.entire 0,.taylor 0,.taylor 1,.taylor 2,.taylor 3,.taylor 4,.entire 1,.taylor 5,.taylor 6,.taylor 7,.taylor 8,.taylor 9,.taylor 10,.entire 2,.taylor 11,.taylor 12,.entire 3,.taylor 13,.taylor 14,.taylor 15,.taylor 16,.taylor 17,.hecke 0,.hecke 1,.hecke 2,.hecke 3,.hecke 4,.hecke 5,.hecke 6,.hecke 7,.hecke 8,.hecke 9,.hecke 10,.hecke 11,.hecke 12,.hecke 13,.hecke 14,.hecke 15,.hecke 16,.hecke 17,.hecke 18,.hecke 19,.hecke 20,.hecke 21,.hecke 22,.hecke 23,.hecke 24,.hecke 25,.hecke 26,.hecke 27,.hecke 28,.hecke 29,.hecke 30,.hecke 31,.hecke 32,.hecke 33,.hecke 34,.hecke 35,.hecke 36,.hecke 37,.hecke 38,.hecke 39,.hecke 40,.hecke 41,.hecke 42,.hecke 43]
def rowKind7 : Fin 114 → RowKind :=
  ![.group 0,.group 1,.group 2,.group 3,.group 4,.group 5,.group 6,.group 7,.group 8,.group 9,.group 10,.group 11,.group 12,.group 13,.center 0,.group 14,.group 15,.group 16,.group 17,.group 18,.group 19,.group 20,.group 21,.group 22,.group 23,.center 1,.group 24,.group 25,.group 26,.group 27,.group 28,.group 29,.group 30,.group 31,.group 32,.group 33,.group 34,.group 35,.group 36,.group 37,.center 2,.group 38,.group 39,.group 40,.group 41,.group 42,.group 43,.group 44,.entire 0,.taylor 0,.taylor 1,.taylor 2,.taylor 3,.taylor 4,.entire 1,.taylor 5,.taylor 6,.taylor 7,.taylor 8,.taylor 9,.taylor 10,.entire 2,.taylor 11,.taylor 12,.entire 3,.taylor 13,.taylor 14,.taylor 15,.taylor 16,.taylor 17,.hecke 0,.hecke 1,.hecke 2,.hecke 3,.hecke 4,.hecke 5,.hecke 6,.hecke 7,.hecke 8,.hecke 9,.hecke 10,.hecke 11,.hecke 12,.hecke 13,.hecke 14,.hecke 15,.hecke 16,.hecke 17,.hecke 18,.hecke 19,.hecke 20,.hecke 21,.hecke 22,.hecke 23,.hecke 24,.hecke 25,.hecke 44,.hecke 27,.hecke 28,.hecke 29,.hecke 30,.hecke 31,.hecke 32,.hecke 33,.hecke 34,.hecke 35,.hecke 36,.hecke 37,.hecke 38,.hecke 39,.hecke 40,.hecke 42,.hecke 45,.hecke 46]
def rowKind (c : Fin 8) : Fin 114 → RowKind := ![rowKind0,rowKind1,rowKind2,rowKind3,rowKind4,rowKind5,rowKind6,rowKind7] c
def heckeSpecs : Fin 47 → ℕ × ℕ := ![(2,2),(2,4),(2,5),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(2,15),(2,16),(2,17),(2,18),(2,20),(2,21),(2,23),(2,24),(2,25),(2,26),(2,27),(2,28),(2,29),(2,30),(2,31),(2,35),(2,36),(2,40),(2,41),(2,42),(2,43),(2,44),(2,46),(2,47),(2,49),(2,50),(3,3),(3,5),(3,6),(3,7),(3,8),(3,9),(3,11),(2,32),(3,12),(3,13)]
def centerSource : Fin 3 → ℕ := ![54,4,111]

def assemble (c : Fin 8) (G : Fin 45 → ℂ) (T : Fin 18 → ℂ) (E : Fin 4 → ℂ)
    (C : Fin 3 → ℂ) (H : Fin 47 → ℂ) (i : Fin 114) : ℂ :=
  match rowKind c i with
  | .group j => G j
  | .taylor j => T j
  | .entire j => E j
  | .center j => C j
  | .hecke j => H j

def leadingRows (c : Fin 8) (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v : Fin 114 → ℂ) : Fin 114 → ℂ :=
  assemble c (fun i => v (gridIndex (groupSource i))-groupCoefficient m i 0 s*v (gridIndex (groupPartner i)))
    (fun i => plusRows v i-rowCoefficient (2*m) f ε i 0 s*minusRows v i) (entireRows v)
    (fun i => v (gridIndex (centerSource i)))
    (fun i => heckeRow (heckeSpecs i).1 (heckeSpecs i).2 m f s v)

def shiftRows (c : Fin 8) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (v : Fin 114 → ℂ) : Fin 114 → ℂ :=
  assemble c (fun i => groupCoefficient m i (n+1) s*v (gridIndex (groupPartner i)))
    (fun i => rowCoefficient (2*m) f ε i (n+1) s*minusRows v i) 0 0 0

def leadingLinear (c : Fin 8) (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : (Fin 114 → ℂ) →ₗ[ℂ] (Fin 114 → ℂ) where
  toFun := leadingRows c m f ε s
  map_add' := by
    intro v w
    funext i
    cases hi : rowKind c i <;>
      simp [leadingRows,assemble,hi,plusRows,minusRows,entireRows,sumRow,heckeRow,Finset.sum_add_distrib] <;> ring
  map_smul' := by
    intro a v
    funext i
    cases hi : rowKind c i <;>
      simp [leadingRows,assemble,hi,plusRows,minusRows,entireRows,sumRow,heckeRow,smul_eq_mul,← Finset.mul_sum] <;> ring

def shiftLinear (c : Fin 8) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : (Fin 114 → ℂ) →ₗ[ℂ] (Fin 114 → ℂ) where
  toFun := shiftRows c m f ε n s
  map_add' := by
    intro v w
    funext i
    cases hi : rowKind c i <;>
      simp [shiftRows,assemble,hi,minusRows,sumRow,Finset.sum_add_distrib] <;> ring
  map_smul' := by
    intro a v
    funext i
    cases hi : rowKind c i <;>
      simp [shiftRows,assemble,hi,minusRows,sumRow,smul_eq_mul,← Finset.mul_sum] <;> ring

def leadingMatrix (c : Fin 8) (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : Matrix (Fin 114) (Fin 114) ℂ :=
  (leadingLinear c m f ε s).toMatrix'
def shiftMatrix (c : Fin 8) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin 114) (Fin 114) ℂ :=
  (shiftLinear c m f ε n s).toMatrix'

theorem leadingMatrix_mulVec (c : Fin 8) (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v : Fin 114 → ℂ) :
    leadingMatrix c m f ε s *ᵥ v=leadingRows c m f ε s v := LinearMap.toMatrix'_mulVec _ _
theorem shiftMatrix_mulVec (c : Fin 8) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (v : Fin 114 → ℂ) :
    shiftMatrix c m f ε n s *ᵥ v=shiftRows c m f ε n s v := LinearMap.toMatrix'_mulVec _ _

#print axioms leadingMatrix_mulVec
#print axioms shiftMatrix_mulVec
end QuantitativeArithmeticSmallLevelNineteenGridSystem
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenGridEntriesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenGridSystem
open Complex Matrix
open QuantitativeArithmeticSmallLevelNineteenGridAnalytic
open QuantitativeArithmeticSmallLevelNineteenGridRamanujan

theorem heckeSpecs_valid (i : Fin 47) : (heckeSpecs i).1.Prime ∧
    ¬(heckeSpecs i).1∣19 ∧ (heckeSpecs i).1∣114 := by fin_cases i <;> decide

theorem taylorCoefficient_analytic (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 18) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (rowCoefficient (2*m) f ε i n) s := by
  apply SmallLevelTaylor.taylorRowScalar_analytic
  · exact_mod_cast Nat.lcm_pos (by decide : 0<19) (pow_pos (specs_valid i).1 2)
  · exact div_ne_zero (by exact_mod_cast (specs_valid i).2.2.1) (by norm_num)

theorem leadingMatrix_apply (c : Fin 8) (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i j : Fin 114) :
    leadingMatrix c m f ε s i j=leadingRows c m f ε s (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _
theorem shiftMatrix_apply (c : Fin 8) (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (i j : Fin 114) :
    shiftMatrix c m f ε n s i j=shiftRows c m f ε n s (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _

theorem leadingMatrix_analytic (c : Fin 8) (m : ℕ) (f : ℕ→ℂ) (ε x : ℂ) (i j : Fin 114) :
    AnalyticAt ℂ (fun s => leadingMatrix c m f ε s i j) x := by
  simp only [leadingMatrix_apply]
  cases hi : rowKind c i with
  | group a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const.sub ((groupCoefficient_analytic m a 0 x).mul analyticAt_const)
  | taylor a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const.sub ((taylorCoefficient_analytic m f ε a 0 x).mul analyticAt_const)
  | entire a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const
  | center a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const
  | hecke a =>
    simp only [leadingRows,assemble,hi,heckeRow]
    have hp := SmallLevelTaylor.hecke_parameter_analytic (heckeSpecs_valid a).1.pos m x
    exact (analyticAt_const.sub ((analyticAt_const.mul hp).mul analyticAt_const)).add
      ((hp.pow 2).mul analyticAt_const)

theorem shiftMatrix_analytic (c : Fin 8) (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (x : ℂ) (i j : Fin 114) :
    AnalyticAt ℂ (fun s => shiftMatrix c m f ε n s i j) x := by
  simp only [shiftMatrix_apply]
  cases hi : rowKind c i with
  | group a =>
    simp only [shiftRows,assemble,hi]
    exact (groupCoefficient_analytic m a (n+1) x).mul analyticAt_const
  | taylor a =>
    simp only [shiftRows,assemble,hi]
    exact (taylorCoefficient_analytic m f ε a (n+1) x).mul analyticAt_const
  | entire a => simp only [shiftRows,assemble,hi,Pi.zero_apply]; exact analyticAt_const
  | center a => simp only [shiftRows,assemble,hi,Pi.zero_apply]; exact analyticAt_const
  | hecke a => simp only [shiftRows,assemble,hi,Pi.zero_apply]; exact analyticAt_const

#print axioms leadingMatrix_analytic
#print axioms shiftMatrix_analytic
end QuantitativeArithmeticSmallLevelNineteenGridSystem
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenGridOriginalSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenGridSystem
open Complex Matrix Set SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelNineteenGridAnalytic
open QuantitativeArithmeticSmallLevelNineteenGridRamanujan
open QuantitativeArithmeticSmallLevelNineteen (exceptionalCenter)

theorem original_center_rows {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) (i : Fin 3) :
    (∀ s : ℂ, AnalyticAt ℂ (exceptionalCenter (2*m) f (centerSource i)) s) ∧
    ∃ B : ℝ, ∀ s : ℂ, B<s.re →
      exceptionalCenter (2*m) f (centerSource i) s=
        gridVector (2*m) f s (gridIndex (centerSource i)) := by
  simp only [gridVector_index,grid,Int.cast_natCast,Nat.cast_ofNat]
  fin_cases i
  · exact QuantitativeArithmeticSmallLevelNineteen.original_exceptional_center54 m hm hf
  · exact QuantitativeArithmeticSmallLevelNineteen.original_exceptional_center4 m hm hf
  · exact QuantitativeArithmeticSmallLevelNineteen.original_exceptional_center111 m hm hf

/-- All eight selected square systems have actual original-input Taylor
identities. Rank and specialization are separate from this analytic assembly. -/
theorem original_matrix_system {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 19 (2*m) f ε) (c : Fin 8) :
    ∃ B : ℝ, ∃ error : ℕ → ℂ → Fin 114 → ℂ,
      (∀ i : Fin 114, ∀ s : ℂ, B<s.re → AnalyticAt ℂ (fun z => gridVector (2*m) f z i) s) ∧
      (∀ M : ℕ, ∀ i : Fin 114, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (fun z => error M z i) s) ∧
      ∀ M : ℕ, ∀ s : ℂ, B<s.re →
        leadingMatrix c m f ε s *ᵥ gridVector (2*m) f s=
          error M s+∑ n∈Finset.range M,
            shiftMatrix c m f ε n s *ᵥ gridVector (2*m) f (s+((n:ℂ)+1)) := by
  obtain ⟨BG,errG,hG⟩ := original_group_system hf
  choose bT hT using fun i : Fin 18 => original_taylor_rows hf ε hlaw i
  obtain ⟨hRE,BR,hR⟩ := original_entire_rows (by omega : 0<2*m) hf
  have hCE := fun i : Fin 3 => (original_center_rows hm hf i).1
  choose bC hC using fun i : Fin 3 => (original_center_rows hm hf i).2
  choose bH hH using fun i : Fin 47 => original_grid_hecke hf
    (heckeSpecs_valid i).1 (heckeSpecs_valid i).2.1 (heckeSpecs_valid i).2.2
  obtain ⟨BF,hF⟩ := original_common_halfplane hf
  let BT : ℝ := Finset.univ.sup' Finset.univ_nonempty bT
  let BC : ℝ := Finset.univ.sup' Finset.univ_nonempty bC
  let BH : ℝ := Finset.univ.sup' Finset.univ_nonempty bH
  let bounds : Fin 6 → ℝ := ![BG,BT,BR,BC,BH,BF]
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty bounds
  have hb (i : Fin 6) : bounds i≤B := Finset.le_sup' bounds (Finset.mem_univ i)
  have hBG : BG≤B := by simpa only [bounds,Matrix.cons_val_zero] using hb 0
  have hBT (i : Fin 18) : bT i≤B :=
    (show bT i≤BT from Finset.le_sup' bT (Finset.mem_univ i)).trans (by simpa only [bounds,Matrix.cons_val] using hb 1)
  have hBR : BR≤B := by simpa [bounds] using hb 2
  have hBC (i : Fin 3) : bC i≤B :=
    (show bC i≤BC from Finset.le_sup' bC (Finset.mem_univ i)).trans (by simpa only [bounds,Matrix.cons_val] using hb 3)
  have hBH (i : Fin 47) : bH i≤B :=
    (show bH i≤BH from Finset.le_sup' bH (Finset.mem_univ i)).trans (by simpa only [bounds,Matrix.cons_val] using hb 4)
  have hBF : BF≤B := by simpa [bounds] using hb 5
  let error : ℕ → ℂ → Fin 114 → ℂ := fun M s =>
    assemble c (fun i => errG i M s) (fun i => rowError (2*m) f ε i M s)
      (fun i => ramanujanEntire 19 (2*m) f (entireSpecs i) s)
      (fun i => exceptionalCenter (2*m) f (centerSource i) s) 0
  refine ⟨B,error,?_,?_,?_⟩
  · intro i s hs
    exact (hF ((i.val:ℝ)/114) s (lt_of_le_of_lt hBF hs)).1
  · intro M i s hs
    have hg' (j : Fin 45) : AnalyticAt ℂ (errG j M) s := by
      apply (hG j M).1 s
      change BG-((M:ℝ)+1)<s.re
      linarith
    have ht' (j : Fin 18) : AnalyticAt ℂ (rowError (2*m) f ε j M) s := by
      apply (hT j M).1 s
      change bT j-((M:ℝ)+1)<s.re
      linarith [hBT j]
    cases hi : rowKind c i with
    | group j => simpa only [error,assemble,hi] using hg' j
    | taylor j => simpa only [error,assemble,hi] using ht' j
    | entire j => simpa only [error,assemble,hi] using hRE j s
    | center j => simpa only [error,assemble,hi] using hCE j s
    | hecke j => simp only [error,assemble,hi,Pi.zero_apply]; exact analyticAt_const
  · intro M s hs
    rw [leadingMatrix_mulVec]
    simp_rw [shiftMatrix_mulVec]
    funext i
    simp only [Pi.add_apply,Finset.sum_apply]
    cases hi : rowKind c i with
    | group j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi] using
        (hG j M).2 s (lt_of_le_of_lt hBG hs)
    | taylor j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi] using
        (hT j M).2 s (lt_of_le_of_lt (hBT j) hs)
    | entire j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,Pi.zero_apply,
        Finset.sum_const_zero,add_zero] using (hR j s (lt_of_le_of_lt hBR hs)).symm
    | center j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,Pi.zero_apply,
        Finset.sum_const_zero,add_zero] using (hC j s (lt_of_le_of_lt (hBC j) hs)).symm
    | hecke j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,Pi.zero_apply,
        Finset.sum_const_zero,add_zero] using
          hH j (heckeSpecs j).2 s (lt_of_le_of_lt (hBH j) hs)

#print axioms original_matrix_system
end QuantitativeArithmeticSmallLevelNineteenGridSystem
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenGridLaurentV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenGridSystem
open Complex SmallLevelTaylor FinitenessNormalizedTwistProduct
open QuantitativeArithmeticSmallLevelNineteenGridAnalytic
open QuantitativeArithmeticSmallLevelNineteenGridRamanujan

def threePrimeMonomial (e : ℤ×ℤ×ℤ) (x y z : ℂ) : ℂ := x^e.1*y^e.2.1*z^e.2.2
def primeParameter (p m : ℕ) (s : ℂ) : ℂ := (p:ℂ)^(s-(m:ℂ))
def phaseRoot (m : ℕ) (ε : ℂ) : ℂ := ε*I^(2*m)
def badNineteen (f : ℕ→ℂ) : ℂ := (Real.sqrt 19:ℂ)*f 19

theorem real_three_prime_power (r : ℝ) (e : ℤ×ℤ×ℤ)
    (hr : r=(2:ℝ)^e.1*(3:ℝ)^e.2.1*(19:ℝ)^e.2.2) (s : ℂ) :
    (r:ℂ)^s=threePrimeMonomial e ((2:ℂ)^s) ((3:ℂ)^s) ((19:ℂ)^s) := by
  rw [hr,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  simp only [Complex.ofReal_zpow]
  rw [QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic.positive_zpow_cpow (by norm_num : (0:ℝ)<2),
    QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic.positive_zpow_cpow (by norm_num : (0:ℝ)<3),
    QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic.positive_zpow_cpow (by norm_num : (0:ℝ)<19)]
  rfl

def groupPowers : Fin 45 → ℤ×ℤ×ℤ := ![(2,0,0),(0,2,0),(2,2,0),(0,2,0),(0,0,0),(2,2,0),(0,2,0),(2,0,0),(-2,2,0),(0,0,0),(2,-2,0),(-2,0,0),(0,-2,0),(-2,-2,0),(-2,-2,0),(0,-2,0),(2,-2,0),(-2,2,0),(2,0,0),(0,2,0),(2,2,0),(0,0,0),(0,0,0),(0,0,0),(-2,0,0),(0,0,0),(2,0,0),(0,-2,0),(0,2,0),(0,0,0),(-2,0,0),(2,0,0),(0,-2,0),(-2,-2,0),(-2,0,0),(-2,2,0),(2,0,0),(0,-2,0),(-2,-2,0),(0,-2,0),(2,-2,0),(-2,2,0),(0,2,0),(2,0,0),(2,2,0)]
theorem group_rate_certificate (i : Fin 45) :
    groupRate i=(2:ℝ)^(groupPowers i).1*(3:ℝ)^(groupPowers i).2.1*(19:ℝ)^(groupPowers i).2.2 := by
  fin_cases i <;> norm_num [groupRate,groupPowers,gC,gD,groupMatrix,groupCenter,groupSource,groupSpecs,
QuantitativeArithmeticSmallLevelNineteen.continuationMatrix,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix0,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix1,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix2,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix3,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix4,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix5,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix6,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix7,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix8,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix9,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix10,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix11,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix12]

def symbolicGroup (X Y Z : ℂ) (i : Fin 45) : ℂ := threePrimeMonomial (groupPowers i) X Y Z

theorem groupCoefficient_laurent (m : ℕ) (s : ℂ) (i : Fin 45) :
    groupCoefficient m i 0 s=symbolicGroup
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 19 m s) i := by
  simp only [groupCoefficient,Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one]
  rw [real_three_prime_power _ _ (group_rate_certificate i)]
  rfl

def taylorPowers : Fin 18 → ℤ×ℤ×ℤ := ![(-2,-2,-1),(-2,2,-1),(-2,2,-1),(-2,-2,1),(-2,-2,1),(-2,0,-1),(-2,0,-1),(0,0,-1),(0,0,-1),(2,0,-1),(2,0,-1),(0,0,-1),(0,0,-1),(-2,-2,0),(-2,-2,0),(0,-2,0),(0,-2,0),(-2,0,0)]
def taylorSign (χ δ : ℂ) (i : Fin 18) : ℂ := if 19∣rowQ i then -χ*δ else χ

def symbolicTaylor (χ δ X Y Z : ℂ) (i : Fin 18) : ℂ :=
  taylorSign χ δ i*threePrimeMonomial (taylorPowers i) X Y Z

theorem taylor_rate_certificate (i : Fin 18) :
    (rowL i:ℝ)*((rowT i:ℝ)/114)^2=
      (2:ℝ)^(taylorPowers i).1*(3:ℝ)^(taylorPowers i).2.1*(19:ℝ)^(taylorPowers i).2.2 := by
  fin_cases i <;> norm_num [rowL,rowQ,rowT,taylorPowers]

theorem root_nineteen (f : ℕ→ℂ) : root 19 f 19= -badNineteen f := by
  have hp : (19:ℕ).primeFactors={19} := (by decide : Nat.Prime 19).primeFactors
  have hv : (19:ℕ).factorization 19=1 := (by decide : Nat.Prime 19).factorization_self
  norm_num [root,hp,hv,FinitenessNormalizedTwistLocal.sign,badNineteen]
  ring

theorem taylor_root_scalar (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 18) :
    root 19 f (rowQ i)*ε*I^(2*m)=taylorSign (phaseRoot m ε) (badNineteen f) i := by
  have hp3 : (3:ℕ).primeFactors={3} := (by decide : Nat.Prime 3).primeFactors
  have hp6 : (6:ℕ).primeFactors={2,3} := by
    rw [show (6:ℕ)=2*3 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  fin_cases i <;> norm_num [rowQ,taylorSign,root_nineteen,root,hp3,hp6,
    FinitenessNormalizedTwistLocal.sign,phaseRoot,badNineteen] <;> ring

theorem taylorCoefficient_laurent (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (i : Fin 18) :
    rowCoefficient (2*m) f ε i 0 s=symbolicTaylor (phaseRoot m ε) (badNineteen f)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 19 m s) i := by
  have hex : s-((2*m:ℕ):ℂ)/2=s-(m:ℂ) := by push_cast; ring
  simp only [rowCoefficient,taylorRowScalar,pow_zero,Ring.choose_zero_right,mul_one,hex,taylor_root_scalar]
  rw [real_three_prime_power _ _ (taylor_rate_certificate i)]
  rfl

#print axioms groupCoefficient_laurent
#print axioms taylorCoefficient_laurent
end QuantitativeArithmeticSmallLevelNineteenGridSystem
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenGridSymbolicV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenGridSystem
open Complex
open QuantitativeArithmeticSmallLevelNineteenGridAnalytic
open QuantitativeArithmeticSmallLevelNineteenGridRamanujan

def symbolicHecke (X Y a b : ℂ) (p t : ℕ) (v : Fin 114 → ℂ) : ℂ :=
  (∑ j∈Finset.range p, v (gridIndex ((t+j*(114/p):ℕ):ℤ)))-
    (if p=2 then a/X else b/Y)*v (gridIndex ((p*t:ℕ):ℤ))+
    (if p=2 then X⁻¹ else Y⁻¹)^2*v (gridIndex ((p^2*t:ℕ):ℤ))

def symbolicRows (c : Fin 8) (χ δ X Y Z a b : ℂ) (v : Fin 114 → ℂ) : Fin 114 → ℂ :=
  assemble c (fun i => v (gridIndex (groupSource i))-symbolicGroup X Y Z i*v (gridIndex (groupPartner i)))
    (fun i => plusRows v i-symbolicTaylor χ δ X Y Z i*minusRows v i) (entireRows v)
    (fun i => v (gridIndex (centerSource i)))
    (fun i => symbolicHecke X Y a b (heckeSpecs i).1 (heckeSpecs i).2 v)

theorem primeParameter_inverse (p m : ℕ) (s : ℂ) :
    (p:ℂ)^((m:ℂ)-s)=(primeParameter p m s)⁻¹ := by
  unfold primeParameter
  rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]

theorem heckeRow_symbolic (p t m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 114 → ℂ)
    (hp : p=2 ∨ p=3) :
    heckeRow p t m f s v=symbolicHecke (primeParameter 2 m s) (primeParameter 3 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) p t v := by
  rcases hp with rfl|rfl <;>
    simp only [heckeRow,symbolicHecke,primeParameter_inverse,show ¬(3:ℕ)=2 by decide,
      ite_true,ite_false,div_eq_mul_inv] <;> norm_num only [Nat.cast_ofNat]

theorem actual_leading_rows (c : Fin 8) (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 114 → ℂ) :
    leadingRows c m f ε s v=symbolicRows c (phaseRoot m ε) (badNineteen f)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 19 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v := by
  funext i
  cases hi : rowKind c i with
  | group j => simp only [leadingRows,symbolicRows,assemble,hi,groupCoefficient_laurent]
  | taylor j => simp only [leadingRows,symbolicRows,assemble,hi,taylorCoefficient_laurent]
  | entire j => simp only [leadingRows,symbolicRows,assemble,hi]
  | center j => simp only [leadingRows,symbolicRows,assemble,hi]
  | hecke j =>
    simp only [leadingRows,symbolicRows,assemble,hi]
    apply heckeRow_symbolic
    fin_cases j <;> decide

#print axioms actual_leading_rows
end QuantitativeArithmeticSmallLevelNineteenGridSystem
end
end
