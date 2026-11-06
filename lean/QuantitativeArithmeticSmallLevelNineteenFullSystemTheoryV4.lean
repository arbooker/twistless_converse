module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import QuantitativeArithmeticSmallLevelNineteenFullGroupTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenFullHeckeRowsV1
public import QuantitativeArithmeticSmallLevelNineteenFullRamanujanTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelNineteenFullSystem. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelNineteenFullSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenFullSystem
open Complex Matrix SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelNineteenFullGroup
open QuantitativeArithmeticSmallLevelNineteenFullRamanujan
open QuantitativeArithmeticSmallLevelNineteenGridAnalytic (gridVector gridIndex gridVector_index heckeRow)

inductive RowKind where
  | group : Fin 516 → RowKind
  | taylor : Fin 96 → RowKind
  | entire : Fin 8 → RowKind
  | center : Fin 13 → RowKind
  | hecke : Fin 101 → RowKind
  deriving DecidableEq

/-- The original754 certificate rows with the repeated cusp rows identified. -/
def rowKind (i : Fin 734) : RowKind :=
  if h : i.val<516 then .group ⟨i.val,h⟩
  else if h : i.val<612 then .taylor ⟨i.val-516,by omega⟩
  else if h : i.val<620 then .entire ⟨i.val-612,by omega⟩
  else if h : i.val<633 then .center ⟨i.val-620,by omega⟩
  else .hecke ⟨i.val-633,by omega⟩

def assemble (G : Fin 516→ℂ) (T : Fin 96→ℂ) (E : Fin 8→ℂ)
    (C : Fin 13→ℂ) (H : Fin 101→ℂ) (i : Fin 734) : ℂ :=
  match rowKind i with
  | .group j => G j
  | .taylor j => T j
  | .entire j => E j
  | .center j => C j
  | .hecke j => H j

def leadingRows (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 114→ℂ) : Fin 734→ℂ :=
  assemble (fun i => v (gridIndex (source i))-coefficient m i 0 s*v (gridIndex (partner i)))
    (fun i => plusRows v i-rowCoefficient (2*m) f ε i 0 s*minusRows v i) (entireRows v)
    (fun i => v (gridIndex (centerGrid i)))
    (fun i => QuantitativeArithmeticSmallLevelNineteenFullHecke.row i m f s v)

def shiftRows (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (v : Fin 114→ℂ) : Fin 734→ℂ :=
  assemble (fun i => coefficient m i (n+1) s*v (gridIndex (partner i)))
    (fun i => rowCoefficient (2*m) f ε i (n+1) s*minusRows v i) 0 0 0

theorem hecke_add (i : Fin 101) (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v w : Fin 114→ℂ) :
    QuantitativeArithmeticSmallLevelNineteenFullHecke.row i m f s (v+w)=
      QuantitativeArithmeticSmallLevelNineteenFullHecke.row i m f s v+
      QuantitativeArithmeticSmallLevelNineteenFullHecke.row i m f s w := by
  unfold QuantitativeArithmeticSmallLevelNineteenFullHecke.row
  split_ifs <;>
    simp [QuantitativeArithmeticSmallLevelNineteenFullHecke.ramifiedRow,heckeRow,
      Finset.sum_add_distrib] <;> ring

theorem hecke_smul (i : Fin 101) (m : ℕ) (f : ℕ→ℂ) (s a : ℂ) (v : Fin 114→ℂ) :
    QuantitativeArithmeticSmallLevelNineteenFullHecke.row i m f s (a • v)=
      a*QuantitativeArithmeticSmallLevelNineteenFullHecke.row i m f s v := by
  unfold QuantitativeArithmeticSmallLevelNineteenFullHecke.row
  split_ifs <;>
    simp [QuantitativeArithmeticSmallLevelNineteenFullHecke.ramifiedRow,heckeRow,
      smul_eq_mul,← Finset.mul_sum] <;> ring

def leadingLinear (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : (Fin 114→ℂ) →ₗ[ℂ] (Fin 734→ℂ) where
  toFun := leadingRows m f ε s
  map_add' := by
    intro v w
    funext i
    cases hi : rowKind i <;>
      simp [leadingRows,assemble,hi,plusRows,minusRows,entireRows,sumRow,
        hecke_add,Finset.sum_add_distrib] <;> ring
  map_smul' := by
    intro a v
    funext i
    cases hi : rowKind i <;>
      simp [leadingRows,assemble,hi,plusRows,minusRows,entireRows,sumRow,
        hecke_smul,smul_eq_mul,← Finset.mul_sum] <;> ring

def shiftLinear (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : (Fin 114→ℂ) →ₗ[ℂ] (Fin 734→ℂ) where
  toFun := shiftRows m f ε n s
  map_add' := by
    intro v w
    funext i
    cases hi : rowKind i <;>
      simp [shiftRows,assemble,hi,minusRows,sumRow,Finset.sum_add_distrib] <;> ring
  map_smul' := by
    intro a v
    funext i
    cases hi : rowKind i <;>
      simp [shiftRows,assemble,hi,minusRows,sumRow,smul_eq_mul,← Finset.mul_sum] <;> ring

def leadingMatrix (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : Matrix (Fin 734) (Fin 114) ℂ :=
  (leadingLinear m f ε s).toMatrix'
def shiftMatrix (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin 734) (Fin 114) ℂ :=
  (shiftLinear m f ε n s).toMatrix'

theorem leadingMatrix_mulVec (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 114→ℂ) :
    leadingMatrix m f ε s *ᵥ v=leadingRows m f ε s v := LinearMap.toMatrix'_mulVec _ _
theorem shiftMatrix_mulVec (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (v : Fin 114→ℂ) :
    shiftMatrix m f ε n s *ᵥ v=shiftRows m f ε n s v := LinearMap.toMatrix'_mulVec _ _

#print axioms leadingMatrix_mulVec
#print axioms shiftMatrix_mulVec
end QuantitativeArithmeticSmallLevelNineteenFullSystem
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenFullEntriesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenFullSystem
open Complex Matrix
open QuantitativeArithmeticSmallLevelNineteenFullGroup
open QuantitativeArithmeticSmallLevelNineteenFullRamanujan

theorem taylorCoefficient_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 96) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (rowCoefficient (2*m) f ε i n) s := by
  apply SmallLevelTaylor.taylorRowScalar_analytic
  · exact_mod_cast Nat.lcm_pos (by decide : 0<19) (pow_pos (specs_valid i).1 2)
  · exact div_ne_zero (by exact_mod_cast (specs_valid i).2.2.1) (by norm_num)

theorem leadingMatrix_apply (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i : Fin 734) (j : Fin 114) :
    leadingMatrix m f ε s i j=leadingRows m f ε s (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _
theorem shiftMatrix_apply (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (i : Fin 734) (j : Fin 114) :
    shiftMatrix m f ε n s i j=shiftRows m f ε n s (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _

theorem leadingMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε x : ℂ) (i : Fin 734) (j : Fin 114) :
    AnalyticAt ℂ (fun s => leadingMatrix m f ε s i j) x := by
  simp only [leadingMatrix_apply]
  cases hi : rowKind i with
  | group a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const.sub ((coefficient_analytic m a 0 x).mul analyticAt_const)
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
    simp only [leadingRows,assemble,hi]
    exact QuantitativeArithmeticSmallLevelNineteenFullHecke.row_analytic a m f _ x

theorem shiftMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (x : ℂ) (i : Fin 734) (j : Fin 114) :
    AnalyticAt ℂ (fun s => shiftMatrix m f ε n s i j) x := by
  simp only [shiftMatrix_apply]
  cases hi : rowKind i with
  | group a =>
    simp only [shiftRows,assemble,hi]
    exact (coefficient_analytic m a (n+1) x).mul analyticAt_const
  | taylor a =>
    simp only [shiftRows,assemble,hi]
    exact (taylorCoefficient_analytic m f ε a (n+1) x).mul analyticAt_const
  | entire a => simp only [shiftRows,assemble,hi,Pi.zero_apply]; exact analyticAt_const
  | center a => simp only [shiftRows,assemble,hi,Pi.zero_apply]; exact analyticAt_const
  | hecke a => simp only [shiftRows,assemble,hi,Pi.zero_apply]; exact analyticAt_const

#print axioms leadingMatrix_analytic
#print axioms shiftMatrix_analytic
end QuantitativeArithmeticSmallLevelNineteenFullSystem
end
end
