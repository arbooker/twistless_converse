module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic
public meta import QuantitativeArithmeticCompactCommandsV1

/-! Consolidated chapter: QuantitativeArithmeticFiniteRowEvaluation. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticFiniteSumEvaluationBundleV4 -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem sum_101 (f : Fin 101→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 + f 48 + f 49 + f 50 + f 51 + f 52 + f 53 + f 54 + f 55 + f 56 + f 57 + f 58 + f 59 + f 60 + f 61 + f 62 + f 63 + f 64 + f 65 + f 66 + f 67 + f 68 + f 69 + f 70 + f 71 + f 72 + f 73 + f 74 + f 75 + f 76 + f 77 + f 78 + f 79 + f 80 + f 81 + f 82 + f 83 + f 84 + f 85 + f 86 + f 87 + f 88 + f 89 + f 90 + f 91 + f 92 + f 93 + f 94 + f 95 + f 96 + f 97 + f 98 + f 99 + f 100 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33 + (f 34 + (f 35 + (f 36 + (f 37 + (f 38 + (f 39 + (f 40 + (f 41 + (f 42 + (f 43 + (f 44 + (f 45 + (f 46 + (f 47 + (f 48 + (f 49 + (f 50 + (f 51 + (f 52 + (f 53 + (f 54 + (f 55 + (f 56 + (f 57 + (f 58 + (f 59 + (f 60 + (f 61 + (f 62 + (f 63 + (f 64 + (f 65 + (f 66 + (f 67 + (f 68 + (f 69 + (f 70 + (f 71 + (f 72 + (f 73 + (f 74 + (f 75 + (f 76 + (f 77 + (f 78 + (f 79 + (f 80 + (f 81 + (f 82 + (f 83 + (f 84 + (f 85 + (f 86 + (f 87 + (f 88 + (f 89 + (f 90 + (f 91 + (f 92 + (f 93 + (f 94 + (f 95 + (f 96 + (f 97 + (f 98 + (f 99 + (f 100)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 + f 48 + f 49 + f 50 + f 51 + f 52 + f 53 + f 54 + f 55 + f 56 + f 57 + f 58 + f 59 + f 60 + f 61 + f 62 + f 63 + f 64 + f 65 + f 66 + f 67 + f 68 + f 69 + f 70 + f 71 + f 72 + f 73 + f 74 + f 75 + f 76 + f 77 + f 78 + f 79 + f 80 + f 81 + f 82 + f 83 + f 84 + f 85 + f 86 + f 87 + f 88 + f 89 + f 90 + f 91 + f 92 + f 93 + f 94 + f 95 + f 96 + f 97 + f 98 + f 99 + f 100
    ac_rfl

theorem sum_103 (f : Fin 103→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 + f 48 + f 49 + f 50 + f 51 + f 52 + f 53 + f 54 + f 55 + f 56 + f 57 + f 58 + f 59 + f 60 + f 61 + f 62 + f 63 + f 64 + f 65 + f 66 + f 67 + f 68 + f 69 + f 70 + f 71 + f 72 + f 73 + f 74 + f 75 + f 76 + f 77 + f 78 + f 79 + f 80 + f 81 + f 82 + f 83 + f 84 + f 85 + f 86 + f 87 + f 88 + f 89 + f 90 + f 91 + f 92 + f 93 + f 94 + f 95 + f 96 + f 97 + f 98 + f 99 + f 100 + f 101 + f 102 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33 + (f 34 + (f 35 + (f 36 + (f 37 + (f 38 + (f 39 + (f 40 + (f 41 + (f 42 + (f 43 + (f 44 + (f 45 + (f 46 + (f 47 + (f 48 + (f 49 + (f 50 + (f 51 + (f 52 + (f 53 + (f 54 + (f 55 + (f 56 + (f 57 + (f 58 + (f 59 + (f 60 + (f 61 + (f 62 + (f 63 + (f 64 + (f 65 + (f 66 + (f 67 + (f 68 + (f 69 + (f 70 + (f 71 + (f 72 + (f 73 + (f 74 + (f 75 + (f 76 + (f 77 + (f 78 + (f 79 + (f 80 + (f 81 + (f 82 + (f 83 + (f 84 + (f 85 + (f 86 + (f 87 + (f 88 + (f 89 + (f 90 + (f 91 + (f 92 + (f 93 + (f 94 + (f 95 + (f 96 + (f 97 + (f 98 + (f 99 + (f 100 + (f 101 + (f 102)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 + f 48 + f 49 + f 50 + f 51 + f 52 + f 53 + f 54 + f 55 + f 56 + f 57 + f 58 + f 59 + f 60 + f 61 + f 62 + f 63 + f 64 + f 65 + f 66 + f 67 + f 68 + f 69 + f 70 + f 71 + f 72 + f 73 + f 74 + f 75 + f 76 + f 77 + f 78 + f 79 + f 80 + f 81 + f 82 + f 83 + f 84 + f 85 + f 86 + f 87 + f 88 + f 89 + f 90 + f 91 + f 92 + f 93 + f 94 + f 95 + f 96 + f 97 + f 98 + f 99 + f 100 + f 101 + f 102
    ac_rfl

theorem sum_10 (f : Fin 10→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9
    ac_rfl

theorem sum_11 (f : Fin 11→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10)))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10
    ac_rfl

theorem sum_12 (f : Fin 12→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11
    ac_rfl

theorem sum_29 (f : Fin 29→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28)))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28
    ac_rfl

theorem sum_31 (f : Fin 31→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30)))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30
    ac_rfl

theorem sum_32 (f : Fin 32→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31
    ac_rfl

theorem sum_33 (f : Fin 33→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32)))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32
    ac_rfl

theorem sum_34 (f : Fin 34→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33))))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33
    ac_rfl

theorem sum_36 (f : Fin 36→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33 + (f 34 + (f 35))))))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35
    ac_rfl

theorem sum_37 (f : Fin 37→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33 + (f 34 + (f 35 + (f 36)))))))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36
    ac_rfl

theorem sum_38 (f : Fin 38→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33 + (f 34 + (f 35 + (f 36 + (f 37))))))))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37
    ac_rfl

theorem sum_40 (f : Fin 40→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33 + (f 34 + (f 35 + (f 36 + (f 37 + (f 38 + (f 39))))))))))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39
    ac_rfl

theorem sum_42 (f : Fin 42→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33 + (f 34 + (f 35 + (f 36 + (f 37 + (f 38 + (f 39 + (f 40 + (f 41))))))))))))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41
    ac_rfl

theorem sum_43 (f : Fin 43→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33 + (f 34 + (f 35 + (f 36 + (f 37 + (f 38 + (f 39 + (f 40 + (f 41 + (f 42)))))))))))))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42
    ac_rfl

theorem sum_48 (f : Fin 48→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33 + (f 34 + (f 35 + (f 36 + (f 37 + (f 38 + (f 39 + (f 40 + (f 41 + (f 42 + (f 43 + (f 44 + (f 45 + (f 46 + (f 47))))))))))))))))))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47
    ac_rfl

theorem sum_4 (f : Fin 4→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3))) = f 0 + f 1 + f 2 + f 3
    ac_rfl

theorem sum_53 (f : Fin 53→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 + f 48 + f 49 + f 50 + f 51 + f 52 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33 + (f 34 + (f 35 + (f 36 + (f 37 + (f 38 + (f 39 + (f 40 + (f 41 + (f 42 + (f 43 + (f 44 + (f 45 + (f 46 + (f 47 + (f 48 + (f 49 + (f 50 + (f 51 + (f 52)))))))))))))))))))))))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 + f 48 + f 49 + f 50 + f 51 + f 52
    ac_rfl

theorem sum_5 (f : Fin 5→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4)))) = f 0 + f 1 + f 2 + f 3 + f 4
    ac_rfl

theorem sum_6 (f : Fin 6→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5
    ac_rfl

theorem sum_75 (f : Fin 75→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 + f 48 + f 49 + f 50 + f 51 + f 52 + f 53 + f 54 + f 55 + f 56 + f 57 + f 58 + f 59 + f 60 + f 61 + f 62 + f 63 + f 64 + f 65 + f 66 + f 67 + f 68 + f 69 + f 70 + f 71 + f 72 + f 73 + f 74 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33 + (f 34 + (f 35 + (f 36 + (f 37 + (f 38 + (f 39 + (f 40 + (f 41 + (f 42 + (f 43 + (f 44 + (f 45 + (f 46 + (f 47 + (f 48 + (f 49 + (f 50 + (f 51 + (f 52 + (f 53 + (f 54 + (f 55 + (f 56 + (f 57 + (f 58 + (f 59 + (f 60 + (f 61 + (f 62 + (f 63 + (f 64 + (f 65 + (f 66 + (f 67 + (f 68 + (f 69 + (f 70 + (f 71 + (f 72 + (f 73 + (f 74)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 + f 48 + f 49 + f 50 + f 51 + f 52 + f 53 + f 54 + f 55 + f 56 + f 57 + f 58 + f 59 + f 60 + f 61 + f 62 + f 63 + f 64 + f 65 + f 66 + f 67 + f 68 + f 69 + f 70 + f 71 + f 72 + f 73 + f 74
    ac_rfl

theorem sum_76 (f : Fin 76→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 + f 48 + f 49 + f 50 + f 51 + f 52 + f 53 + f 54 + f 55 + f 56 + f 57 + f 58 + f 59 + f 60 + f 61 + f 62 + f 63 + f 64 + f 65 + f 66 + f 67 + f 68 + f 69 + f 70 + f 71 + f 72 + f 73 + f 74 + f 75 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + (f 29 + (f 30 + (f 31 + (f 32 + (f 33 + (f 34 + (f 35 + (f 36 + (f 37 + (f 38 + (f 39 + (f 40 + (f 41 + (f 42 + (f 43 + (f 44 + (f 45 + (f 46 + (f 47 + (f 48 + (f 49 + (f 50 + (f 51 + (f 52 + (f 53 + (f 54 + (f 55 + (f 56 + (f 57 + (f 58 + (f 59 + (f 60 + (f 61 + (f 62 + (f 63 + (f 64 + (f 65 + (f 66 + (f 67 + (f 68 + (f 69 + (f 70 + (f 71 + (f 72 + (f 73 + (f 74 + (f 75))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 + f 48 + f 49 + f 50 + f 51 + f 52 + f 53 + f 54 + f 55 + f 56 + f 57 + f 58 + f 59 + f 60 + f 61 + f 62 + f 63 + f 64 + f 65 + f 66 + f 67 + f 68 + f 69 + f 70 + f 71 + f 72 + f 73 + f 74 + f 75
    ac_rfl

theorem sum_7 (f : Fin 7→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6)))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6
    ac_rfl

theorem sum_8 (f : Fin 8→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7
    ac_rfl

theorem sum_9 (f : Fin 9→ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  all_goals
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8)))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenPoleLeadingCase1EvaluationBundleV4 -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 8192
-- Generated proofs deliberately omit editor info trees.
set_option linter.unreachableTactic false
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

compact_certificate theorem dot_11_1024_case1 (c0 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,c0] v = c0*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 10 = c0*v 10
    ac_rfl
compact_certificate theorem dot_11_133_case1 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,c1,0,0,0,0,c2,0,0,0] v = c0*v 0 + c1*v 2 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 7)) = c0*v 0 + c1*v 2 + c2*v 7
    ac_rfl
compact_certificate theorem dot_11_135_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,c1,c2,0,0,0,0,c3,0,0,0] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 7))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 7
    ac_rfl
compact_certificate theorem dot_11_141_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,c1,c2,0,0,0,c3,0,0,0] v = c0*v 0 + c1*v 2 + c2*v 3 + c3*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 3 + (c3*v 7))) = c0*v 0 + c1*v 2 + c2*v 3 + c3*v 7
    ac_rfl
compact_certificate theorem dot_11_1618_case1 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,c2,0,0,c3,c4] v = c0*v 1 + c1*v 4 + c2*v 6 + c3*v 9 + c4*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4 + (c2*v 6 + (c3*v 9 + (c4*v 10)))) = c0*v 1 + c1*v 4 + c2*v 6 + c3*v 9 + c4*v 10
    ac_rfl
compact_certificate theorem dot_11_16_case1 (c0 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,0,0,c0,0,0,0,0,0,0] v = c0*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 = c0*v 4
    ac_rfl
compact_certificate theorem dot_11_328_case1 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,0,c0,0,0,c1,0,c2,0,0] v = c0*v 3 + c1*v 6 + c2*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 6 + (c2*v 8)) = c0*v 3 + c1*v 6 + c2*v 8
    ac_rfl
compact_certificate theorem dot_11_33_case1 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,0,0,0,c1,0,0,0,0,0] v = c0*v 0 + c1*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 5) = c0*v 0 + c1*v 5
    ac_rfl
compact_certificate theorem dot_11_389_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,c1,0,0,0,0,c2,c3,0,0] v = c0*v 0 + c1*v 2 + c2*v 7 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 7 + (c3*v 8))) = c0*v 0 + c1*v 2 + c2*v 7 + c3*v 8
    ac_rfl
compact_certificate theorem dot_11_544_case1 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,c1,0] v = c0*v 5 + c1*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 9) = c0*v 5 + c1*v 9
    ac_rfl

compact_certificate theorem dot_36_1207967776_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,c3,0,0,0,0,0] v = c0*v 5 + c1*v 13 + c2*v 27 + c3*v 30 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 13 + (c2*v 27 + (c3*v 30))) = c0*v 5 + c1*v 13 + c2*v 27 + c3*v 30
    ac_rfl
compact_certificate theorem dot_36_12320_case1 (c0 c1 c2 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,c1,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 12 + c2*v 13 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 12 + (c2*v 13)) = c0*v 5 + c1*v 12 + c2*v 13
    ac_rfl
compact_certificate theorem dot_36_131072_case1 (c0 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 17 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 17 = c0*v 17
    ac_rfl
compact_certificate theorem dot_36_134217824_case1 (c0 c1 c2 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 6 + c2*v 27 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 6 + (c2*v 27)) = c0*v 5 + c1*v 6 + c2*v 27
    ac_rfl
compact_certificate theorem dot_36_134217984_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0] v = c0*v 8 + c1*v 27 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 + (c1*v 27) = c0*v 8 + c1*v 27
    ac_rfl
compact_certificate theorem dot_36_134226432_case1 (c0 c1 c2 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0] v = c0*v 9 + c1*v 13 + c2*v 27 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 9 + (c1*v 13 + (c2*v 27)) = c0*v 9 + c1*v 13 + c2*v 27
    ac_rfl
compact_certificate theorem dot_36_16416_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14) = c0*v 5 + c1*v 14
    ac_rfl
compact_certificate theorem dot_36_16785440_case1 (c0 c1 c2 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 13 + c2*v 24 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 13 + (c2*v 24)) = c0*v 5 + c1*v 13 + c2*v 24
    ac_rfl
compact_certificate theorem dot_36_17179869184_case1 (c0 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0] v = c0*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 34 = c0*v 34
    ac_rfl
compact_certificate theorem dot_36_1_case1 (c0 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 0 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 = c0*v 0
    ac_rfl
compact_certificate theorem dot_36_2097156_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 2 + c1*v 21 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 21) = c0*v 2 + c1*v 21
    ac_rfl
compact_certificate theorem dot_36_2097184_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 21 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 21) = c0*v 5 + c1*v 21
    ac_rfl
compact_certificate theorem dot_36_2149580800_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0] v = c0*v 21 + c1*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 21 + (c1*v 31) = c0*v 21 + c1*v 31
    ac_rfl
compact_certificate theorem dot_36_262144_case1 (c0 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 18 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 18 = c0*v 18
    ac_rfl
compact_certificate theorem dot_36_268435968_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0] v = c0*v 9 + c1*v 28 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 9 + (c1*v 28) = c0*v 9 + c1*v 28
    ac_rfl
compact_certificate theorem dot_36_2_case1 (c0 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 1 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 = c0*v 1
    ac_rfl
compact_certificate theorem dot_36_32800_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 15 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 15) = c0*v 5 + c1*v 15
    ac_rfl
compact_certificate theorem dot_36_33556480_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0] v = c0*v 11 + c1*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 11 + (c1*v 25) = c0*v 11 + c1*v 25
    ac_rfl
compact_certificate theorem dot_36_34359738368_case1 (c0 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0] v = c0*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 35 = c0*v 35
    ac_rfl
compact_certificate theorem dot_36_4194336_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 22 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 22) = c0*v 5 + c1*v 22
    ac_rfl
compact_certificate theorem dot_36_4303355904_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0] v = c0*v 23 + c1*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 23 + (c1*v 32) = c0*v 23 + c1*v 32
    ac_rfl
compact_certificate theorem dot_36_524288_case1 (c0 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 19 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 19 = c0*v 19
    ac_rfl
compact_certificate theorem dot_36_536871040_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0] v = c0*v 7 + c1*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 29) = c0*v 7 + c1*v 29
    ac_rfl
compact_certificate theorem dot_36_536871968_case1 (c0 c1 c2 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0] v = c0*v 5 + c1*v 10 + c2*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 10 + (c2*v 29)) = c0*v 5 + c1*v 10 + c2*v 29
    ac_rfl
compact_certificate theorem dot_36_537919488_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0] v = c0*v 20 + c1*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 20 + (c1*v 29) = c0*v 20 + c1*v 29
    ac_rfl
compact_certificate theorem dot_36_603979808_case1 (c0 c1 c2 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,c2,0,0,0,0,0,0] v = c0*v 5 + c1*v 26 + c2*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 26 + (c2*v 29)) = c0*v 5 + c1*v 26 + c2*v 29
    ac_rfl
compact_certificate theorem dot_36_65664_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 7 + c1*v 16 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 16) = c0*v 7 + c1*v 16
    ac_rfl
compact_certificate theorem dot_36_68719476735_case1 (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 7 + c8*v 8 + c9*v 9 + c10*v 10 + c11*v 11 + c12*v 12 + c13*v 13 + c14*v 14 + c15*v 15 + c16*v 16 + c17*v 17 + c18*v 18 + c19*v 19 + c20*v 20 + c21*v 21 + c22*v 22 + c23*v 23 + c24*v 24 + c25*v 25 + c26*v 26 + c27*v 27 + c28*v 28 + c29*v 29 + c30*v 30 + c31*v 31 + c32*v 32 + c33*v 33 + c34*v 34 + c35*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 3 + (c4*v 4 + (c5*v 5 + (c6*v 6 + (c7*v 7 + (c8*v 8 + (c9*v 9 + (c10*v 10 + (c11*v 11 + (c12*v 12 + (c13*v 13 + (c14*v 14 + (c15*v 15 + (c16*v 16 + (c17*v 17 + (c18*v 18 + (c19*v 19 + (c20*v 20 + (c21*v 21 + (c22*v 22 + (c23*v 23 + (c24*v 24 + (c25*v 25 + (c26*v 26 + (c27*v 27 + (c28*v 28 + (c29*v 29 + (c30*v 30 + (c31*v 31 + (c32*v 32 + (c33*v 33 + (c34*v 34 + (c35*v 35))))))))))))))))))))))))))))))))))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 7 + c8*v 8 + c9*v 9 + c10*v 10 + c11*v 11 + c12*v 12 + c13*v 13 + c14*v 14 + c15*v 15 + c16*v 16 + c17*v 17 + c18*v 18 + c19*v 19 + c20*v 20 + c21*v 21 + c22*v 22 + c23*v 23 + c24*v 24 + c25*v 25 + c26*v 26 + c27*v 27 + c28*v 28 + c29*v 29 + c30*v 30 + c31*v 31 + c32*v 32 + c33*v 33 + c34*v 34 + c35*v 35
    ac_rfl
compact_certificate theorem dot_36_8208_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 4 + c1*v 13 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 + (c1*v 13) = c0*v 4 + c1*v 13
    ac_rfl
compact_certificate theorem dot_36_8396800_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 13 + c1*v 23 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 13 + (c1*v 23) = c0*v 13 + c1*v 23
    ac_rfl
compact_certificate theorem dot_36_8589934624_case1 (c0 c1 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0] v = c0*v 5 + c1*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 33) = c0*v 5 + c1*v 33
    ac_rfl
compact_certificate theorem dot_36_8_case1 (c0 : ℂ) (v : Fin 36→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 3 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 = c0*v 3
    ac_rfl

compact_certificate theorem dot_39_1048576_case1 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 20 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 20 = c0*v 20
    ac_rfl
compact_certificate theorem dot_39_131136_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17) = c0*v 6 + c1*v 17
    ac_rfl
compact_certificate theorem dot_39_134221824_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 27 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 27) = c0*v 12 + c1*v 27
    ac_rfl
compact_certificate theorem dot_39_137438953728_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0] v = c0*v 8 + c1*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 + (c1*v 37) = c0*v 8 + c1*v 37
    ac_rfl
compact_certificate theorem dot_39_1610612800_case1 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,c2,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 29 + c2*v 30 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 29 + (c2*v 30)) = c0*v 6 + c1*v 29 + c2*v 30
    ac_rfl
compact_certificate theorem dot_39_16_case1 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 = c0*v 4
    ac_rfl
compact_certificate theorem dot_39_17188257792_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0] v = c0*v 23 + c1*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 23 + (c1*v 34) = c0*v 23 + c1*v 34
    ac_rfl
compact_certificate theorem dot_39_18496_case1 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,c1,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 11 + c2*v 14 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 11 + (c2*v 14)) = c0*v 6 + c1*v 11 + c2*v 14
    ac_rfl
compact_certificate theorem dot_39_1_case1 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 0 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 = c0*v 0
    ac_rfl
compact_certificate theorem dot_39_2097152_case1 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 21 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 21 = c0*v 21
    ac_rfl
compact_certificate theorem dot_39_2147483904_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0] v = c0*v 8 + c1*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 + (c1*v 31) = c0*v 8 + c1*v 31
    ac_rfl
compact_certificate theorem dot_39_2164326400_case1 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,c2,0,0,0,0,0,0,0] v = c0*v 16 + c1*v 24 + c2*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 16 + (c1*v 24 + (c2*v 31)) = c0*v 16 + c1*v 24 + c2*v 31
    ac_rfl
compact_certificate theorem dot_39_263168_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 10 + c1*v 18 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 10 + (c1*v 18) = c0*v 10 + c1*v 18
    ac_rfl
compact_certificate theorem dot_39_274877906944_case1 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0] v = c0*v 38 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 38 = c0*v 38
    ac_rfl
compact_certificate theorem dot_39_2_case1 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 1 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 = c0*v 1
    ac_rfl
compact_certificate theorem dot_39_32800_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 15 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 15) = c0*v 5 + c1*v 15
    ac_rfl
compact_certificate theorem dot_39_32832_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 15 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 15) = c0*v 6 + c1*v 15
    ac_rfl
compact_certificate theorem dot_39_33554440_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 3 + c1*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 25) = c0*v 3 + c1*v 25
    ac_rfl
compact_certificate theorem dot_39_33570816_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 14 + c1*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 14 + (c1*v 25) = c0*v 14 + c1*v 25
    ac_rfl
compact_certificate theorem dot_39_34493956096_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0] v = c0*v 27 + c1*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 27 + (c1*v 35) = c0*v 27 + c1*v 35
    ac_rfl
compact_certificate theorem dot_39_4160_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 12 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 12) = c0*v 6 + c1*v 12
    ac_rfl
compact_certificate theorem dot_39_4294984192_case1 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,c0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0] v = c0*v 9 + c1*v 14 + c2*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 9 + (c1*v 14 + (c2*v 32)) = c0*v 9 + c1*v 14 + c2*v 32
    ac_rfl
compact_certificate theorem dot_39_4299161600_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0] v = c0*v 22 + c1*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 22 + (c1*v 32) = c0*v 22 + c1*v 32
    ac_rfl
compact_certificate theorem dot_39_4831854656_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,c3,0,0,0,0,0,0] v = c0*v 6 + c1*v 14 + c2*v 29 + c3*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 14 + (c2*v 29 + (c3*v 32))) = c0*v 6 + c1*v 14 + c2*v 29 + c3*v 32
    ac_rfl
compact_certificate theorem dot_39_4_case1 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 2 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 = c0*v 2
    ac_rfl
compact_certificate theorem dot_39_524288_case1 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 19 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 19 = c0*v 19
    ac_rfl
compact_certificate theorem dot_39_536871104_case1 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 7 + c2*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 7 + (c2*v 29)) = c0*v 6 + c1*v 7 + c2*v 29
    ac_rfl
compact_certificate theorem dot_39_536887360_case1 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 14 + c2*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 14 + (c2*v 29)) = c0*v 6 + c1*v 14 + c2*v 29
    ac_rfl
compact_certificate theorem dot_39_536888320_case1 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0] v = c0*v 10 + c1*v 14 + c2*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 10 + (c1*v 14 + (c2*v 29)) = c0*v 10 + c1*v 14 + c2*v 29
    ac_rfl
compact_certificate theorem dot_39_536952896_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 14 + c2*v 16 + c3*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 14 + (c2*v 16 + (c3*v 29))) = c0*v 6 + c1*v 14 + c2*v 16 + c3*v 29
    ac_rfl
compact_certificate theorem dot_39_545460813759_case1 (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![c0,c1,c2,c3,c4,c5,0,c6,c7,c8,c9,c10,c11,c12,c13,0,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,0,c30,c31,c32,c33,c34,c35] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 7 + c7*v 8 + c8*v 9 + c9*v 10 + c10*v 11 + c11*v 12 + c12*v 13 + c13*v 14 + c14*v 16 + c15*v 17 + c16*v 18 + c17*v 19 + c18*v 20 + c19*v 21 + c20*v 22 + c21*v 23 + c22*v 24 + c23*v 25 + c24*v 26 + c25*v 27 + c26*v 28 + c27*v 29 + c28*v 30 + c29*v 31 + c30*v 33 + c31*v 34 + c32*v 35 + c33*v 36 + c34*v 37 + c35*v 38 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 3 + (c4*v 4 + (c5*v 5 + (c6*v 7 + (c7*v 8 + (c8*v 9 + (c9*v 10 + (c10*v 11 + (c11*v 12 + (c12*v 13 + (c13*v 14 + (c14*v 16 + (c15*v 17 + (c16*v 18 + (c17*v 19 + (c18*v 20 + (c19*v 21 + (c20*v 22 + (c21*v 23 + (c22*v 24 + (c23*v 25 + (c24*v 26 + (c25*v 27 + (c26*v 28 + (c27*v 29 + (c28*v 30 + (c29*v 31 + (c30*v 33 + (c31*v 34 + (c32*v 35 + (c33*v 36 + (c34*v 37 + (c35*v 38))))))))))))))))))))))))))))))))))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 7 + c7*v 8 + c8*v 9 + c9*v 10 + c10*v 11 + c11*v 12 + c12*v 13 + c13*v 14 + c14*v 16 + c15*v 17 + c16*v 18 + c17*v 19 + c18*v 20 + c19*v 21 + c20*v 22 + c21*v 23 + c22*v 24 + c23*v 25 + c24*v 26 + c25*v 27 + c26*v 28 + c27*v 29 + c28*v 30 + c29*v 31 + c30*v 33 + c31*v 34 + c32*v 35 + c33*v 36 + c34*v 37 + c35*v 38
    ac_rfl
compact_certificate theorem dot_39_67108928_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 26 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 26) = c0*v 6 + c1*v 26
    ac_rfl
compact_certificate theorem dot_39_68719476736_case1 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0] v = c0*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 36 = c0*v 36
    ac_rfl
compact_certificate theorem dot_39_805306432_case1 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,c2,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 28 + c2*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 28 + (c2*v 29)) = c0*v 6 + c1*v 28 + c2*v 29
    ac_rfl
compact_certificate theorem dot_39_8256_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 13 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 13) = c0*v 6 + c1*v 13
    ac_rfl
compact_certificate theorem dot_39_8388672_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 23 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 23) = c0*v 6 + c1*v 23
    ac_rfl
compact_certificate theorem dot_39_8589934656_case1 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0] v = c0*v 6 + c1*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 33) = c0*v 6 + c1*v 33
    ac_rfl

compact_certificate theorem dot_40_1048576_case1 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 20 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 20 = c0*v 20
    ac_rfl
compact_certificate theorem dot_40_1073741984_case1 (c0 c1 c2 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 7 + c2*v 30 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 7 + (c2*v 30)) = c0*v 5 + c1*v 7 + c2*v 30
    ac_rfl
compact_certificate theorem dot_40_1073759232_case1 (c0 c1 c2 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0] v = c0*v 10 + c1*v 14 + c2*v 30 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 10 + (c1*v 14 + (c2*v 30)) = c0*v 10 + c1*v 14 + c2*v 30
    ac_rfl
compact_certificate theorem dot_40_1073760288_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,c1,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 11 + c2*v 14 + c3*v 30 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 11 + (c2*v 14 + (c3*v 30))) = c0*v 5 + c1*v 11 + c2*v 14 + c3*v 30
    ac_rfl
compact_certificate theorem dot_40_1073774624_case1 (c0 c1 c2 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 15 + c2*v 30 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 15 + (c2*v 30)) = c0*v 5 + c1*v 15 + c2*v 30
    ac_rfl
compact_certificate theorem dot_40_1075838976_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0] v = c0*v 21 + c1*v 30 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 21 + (c1*v 30) = c0*v 21 + c1*v 30
    ac_rfl
compact_certificate theorem dot_40_1082294009727_case1 (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![c0,c1,c2,c3,c4,c5,c6,0,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,0,c21,c22,0,c23,c24,c25,c26,c27,c28,c29,c30,0,c31,c32,c33,c34,c35] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 8 + c8*v 9 + c9*v 10 + c10*v 11 + c11*v 12 + c12*v 13 + c13*v 14 + c14*v 15 + c15*v 16 + c16*v 17 + c17*v 18 + c18*v 19 + c19*v 20 + c20*v 21 + c21*v 23 + c22*v 24 + c23*v 26 + c24*v 27 + c25*v 28 + c26*v 29 + c27*v 30 + c28*v 31 + c29*v 32 + c30*v 33 + c31*v 35 + c32*v 36 + c33*v 37 + c34*v 38 + c35*v 39 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 3 + (c4*v 4 + (c5*v 5 + (c6*v 6 + (c7*v 8 + (c8*v 9 + (c9*v 10 + (c10*v 11 + (c11*v 12 + (c12*v 13 + (c13*v 14 + (c14*v 15 + (c15*v 16 + (c16*v 17 + (c17*v 18 + (c18*v 19 + (c19*v 20 + (c20*v 21 + (c21*v 23 + (c22*v 24 + (c23*v 26 + (c24*v 27 + (c25*v 28 + (c26*v 29 + (c27*v 30 + (c28*v 31 + (c29*v 32 + (c30*v 33 + (c31*v 35 + (c32*v 36 + (c33*v 37 + (c34*v 38 + (c35*v 39))))))))))))))))))))))))))))))))))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 8 + c8*v 9 + c9*v 10 + c10*v 11 + c11*v 12 + c12*v 13 + c13*v 14 + c14*v 15 + c15*v 16 + c16*v 17 + c17*v 18 + c18*v 19 + c19*v 20 + c20*v 21 + c21*v 23 + c22*v 24 + c23*v 26 + c24*v 27 + c25*v 28 + c26*v 29 + c27*v 30 + c28*v 31 + c29*v 32 + c30*v 33 + c31*v 35 + c32*v 36 + c33*v 37 + c34*v 38 + c35*v 39
    ac_rfl
compact_certificate theorem dot_40_131200_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 7 + c1*v 17 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 17) = c0*v 7 + c1*v 17
    ac_rfl
compact_certificate theorem dot_40_134217760_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 27 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 27) = c0*v 5 + c1*v 27
    ac_rfl
compact_certificate theorem dot_40_137438969856_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0] v = c0*v 14 + c1*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 14 + (c1*v 37) = c0*v 14 + c1*v 37
    ac_rfl
compact_certificate theorem dot_40_17179869728_case1 (c0 c1 c2 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0] v = c0*v 5 + c1*v 9 + c2*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 9 + (c2*v 34)) = c0*v 5 + c1*v 9 + c2*v 34
    ac_rfl
compact_certificate theorem dot_40_18253627424_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,c3,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 30 + c3*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 30 + (c3*v 34))) = c0*v 5 + c1*v 14 + c2*v 30 + c3*v 34
    ac_rfl
compact_certificate theorem dot_40_1_case1 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 0 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 = c0*v 0
    ac_rfl
compact_certificate theorem dot_40_262144_case1 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 18 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 18 = c0*v 18
    ac_rfl
compact_certificate theorem dot_40_268439552_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 28 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 28) = c0*v 12 + c1*v 28
    ac_rfl
compact_certificate theorem dot_40_274877906944_case1 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0] v = c0*v 38 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 38 = c0*v 38
    ac_rfl
compact_certificate theorem dot_40_2_case1 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 1 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 = c0*v 1
    ac_rfl
compact_certificate theorem dot_40_3221241888_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,c3,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 30 + c3*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 30 + (c3*v 31))) = c0*v 5 + c1*v 14 + c2*v 30 + c3*v 31
    ac_rfl
compact_certificate theorem dot_40_33554464_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 25) = c0*v 5 + c1*v 25
    ac_rfl
compact_certificate theorem dot_40_34393292800_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0] v = c0*v 25 + c1*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 25 + (c1*v 35) = c0*v 25 + c1*v 35
    ac_rfl
compact_certificate theorem dot_40_4112_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 4 + c1*v 12 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 + (c1*v 12) = c0*v 4 + c1*v 12
    ac_rfl
compact_certificate theorem dot_40_4128_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 12 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 12) = c0*v 5 + c1*v 12
    ac_rfl
compact_certificate theorem dot_40_4194308_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 2 + c1*v 22 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 22) = c0*v 2 + c1*v 22
    ac_rfl
compact_certificate theorem dot_40_4294967552_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0] v = c0*v 8 + c1*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 + (c1*v 32) = c0*v 8 + c1*v 32
    ac_rfl
compact_certificate theorem dot_40_4299161600_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0] v = c0*v 22 + c1*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 22 + (c1*v 32) = c0*v 22 + c1*v 32
    ac_rfl
compact_certificate theorem dot_40_4311777280_case1 (c0 c1 c2 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0] v = c0*v 15 + c1*v 24 + c2*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 15 + (c1*v 24 + (c2*v 32)) = c0*v 15 + c1*v 24 + c2*v 32
    ac_rfl
compact_certificate theorem dot_40_524288_case1 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 19 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 19 = c0*v 19
    ac_rfl
compact_certificate theorem dot_40_5368725536_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,c3,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 30 + c3*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 30 + (c3*v 32))) = c0*v 5 + c1*v 14 + c2*v 30 + c3*v 32
    ac_rfl
compact_certificate theorem dot_40_536887328_case1 (c0 c1 c2 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 29)) = c0*v 5 + c1*v 14 + c2*v 29
    ac_rfl
compact_certificate theorem dot_40_549755813888_case1 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0] v = c0*v 39 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 39 = c0*v 39
    ac_rfl
compact_certificate theorem dot_40_65568_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 16 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 16) = c0*v 5 + c1*v 16
    ac_rfl
compact_certificate theorem dot_40_67125248_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 14 + c1*v 26 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 14 + (c1*v 26) = c0*v 14 + c1*v 26
    ac_rfl
compact_certificate theorem dot_40_68719476736_case1 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0] v = c0*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 36 = c0*v 36
    ac_rfl
compact_certificate theorem dot_40_8388640_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 23 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 23) = c0*v 5 + c1*v 23
    ac_rfl
compact_certificate theorem dot_40_8396800_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 13 + c1*v 23 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 13 + (c1*v 23) = c0*v 13 + c1*v 23
    ac_rfl
compact_certificate theorem dot_40_8_case1 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 3 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 = c0*v 3
    ac_rfl
compact_certificate theorem dot_40_9663692832_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,c3,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 30 + c3*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 30 + (c3*v 33))) = c0*v 5 + c1*v 14 + c2*v 30 + c3*v 33
    ac_rfl
compact_certificate theorem dot_40_96_case1 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 6) = c0*v 5 + c1*v 6
    ac_rfl

compact_certificate theorem dot_44_1048640_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 20 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 20) = c0*v 6 + c1*v 20
    ac_rfl
compact_certificate theorem dot_44_1073873408_case1 (c0 c1 c2 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 9 + c1*v 17 + c2*v 30 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 9 + (c1*v 17 + (c2*v 30)) = c0*v 9 + c1*v 17 + c2*v 30
    ac_rfl
compact_certificate theorem dot_44_1099511627776_case1 (c0 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0] v = c0*v 40 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 40 = c0*v 40
    ac_rfl
compact_certificate theorem dot_44_134348800_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 17 + c1*v 27 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 17 + (c1*v 27) = c0*v 17 + c1*v 27
    ac_rfl
compact_certificate theorem dot_44_137438969856_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0] v = c0*v 14 + c1*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 14 + (c1*v 37) = c0*v 14 + c1*v 37
    ac_rfl
compact_certificate theorem dot_44_15285788552703_case1 (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![c0,c1,c2,c3,c4,c5,c6,c7,c8,0,c9,c10,0,c11,0,0,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,0,c28,c29,0,0,c30,c31,c32,c33,0,c34,c35] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 7 + c8*v 8 + c9*v 10 + c10*v 11 + c11*v 13 + c12*v 16 + c13*v 17 + c14*v 18 + c15*v 19 + c16*v 20 + c17*v 21 + c18*v 22 + c19*v 23 + c20*v 24 + c21*v 25 + c22*v 26 + c23*v 27 + c24*v 28 + c25*v 29 + c26*v 30 + c27*v 31 + c28*v 33 + c29*v 34 + c30*v 37 + c31*v 38 + c32*v 39 + c33*v 40 + c34*v 42 + c35*v 43 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 3 + (c4*v 4 + (c5*v 5 + (c6*v 6 + (c7*v 7 + (c8*v 8 + (c9*v 10 + (c10*v 11 + (c11*v 13 + (c12*v 16 + (c13*v 17 + (c14*v 18 + (c15*v 19 + (c16*v 20 + (c17*v 21 + (c18*v 22 + (c19*v 23 + (c20*v 24 + (c21*v 25 + (c22*v 26 + (c23*v 27 + (c24*v 28 + (c25*v 29 + (c26*v 30 + (c27*v 31 + (c28*v 33 + (c29*v 34 + (c30*v 37 + (c31*v 38 + (c32*v 39 + (c33*v 40 + (c34*v 42 + (c35*v 43))))))))))))))))))))))))))))))))))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 7 + c8*v 8 + c9*v 10 + c10*v 11 + c11*v 13 + c12*v 16 + c13*v 17 + c14*v 18 + c15*v 19 + c16*v 20 + c17*v 21 + c18*v 22 + c19*v 23 + c20*v 24 + c21*v 25 + c22*v 26 + c23*v 27 + c24*v 28 + c25*v 29 + c26*v 30 + c27*v 31 + c28*v 33 + c29*v 34 + c30*v 37 + c31*v 38 + c32*v 39 + c33*v 40 + c34*v 42 + c35*v 43
    ac_rfl
compact_certificate theorem dot_44_163904_case1 (c0 c1 c2 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 15 + c2*v 17 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 15 + (c2*v 17)) = c0*v 6 + c1*v 15 + c2*v 17
    ac_rfl
compact_certificate theorem dot_44_16448_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 14 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 14) = c0*v 6 + c1*v 14
    ac_rfl
compact_certificate theorem dot_44_16_case1 (c0 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 = c0*v 4
    ac_rfl
compact_certificate theorem dot_44_17179869192_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0] v = c0*v 3 + c1*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 34) = c0*v 3 + c1*v 34
    ac_rfl
compact_certificate theorem dot_44_17179869440_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0] v = c0*v 8 + c1*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 + (c1*v 34) = c0*v 8 + c1*v 34
    ac_rfl
compact_certificate theorem dot_44_17196650496_case1 (c0 c1 c2 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 24 + c2*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 24 + (c2*v 34)) = c0*v 12 + c1*v 24 + c2*v 34
    ac_rfl
compact_certificate theorem dot_44_19327352928_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,c3,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 6 + c2*v 31 + c3*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 6 + (c2*v 31 + (c3*v 34))) = c0*v 5 + c1*v 6 + c2*v 31 + c3*v 34
    ac_rfl
compact_certificate theorem dot_44_19327483968_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,c3,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 + c2*v 31 + c3*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17 + (c2*v 31 + (c3*v 34))) = c0*v 6 + c1*v 17 + c2*v 31 + c3*v 34
    ac_rfl
compact_certificate theorem dot_44_1_case1 (c0 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 0 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 = c0*v 0
    ac_rfl
compact_certificate theorem dot_44_2050_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 1 + c1*v 11 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 11) = c0*v 1 + c1*v 11
    ac_rfl
compact_certificate theorem dot_44_2097152_case1 (c0 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 21 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 21 = c0*v 21
    ac_rfl
compact_certificate theorem dot_44_2147549248_case1 (c0 c1 c2 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 16 + c2*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 16 + (c2*v 31)) = c0*v 6 + c1*v 16 + c2*v 31
    ac_rfl
compact_certificate theorem dot_44_2147614784_case1 (c0 c1 c2 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 + c2*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17 + (c2*v 31)) = c0*v 6 + c1*v 17 + c2*v 31
    ac_rfl
compact_certificate theorem dot_44_2147616768_case1 (c0 c1 c2 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 11 + c1*v 17 + c2*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 11 + (c1*v 17 + (c2*v 31)) = c0*v 11 + c1*v 17 + c2*v 31
    ac_rfl
compact_certificate theorem dot_44_2147618880_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,c1,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 12 + c2*v 17 + c3*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 12 + (c2*v 17 + (c3*v 31))) = c0*v 6 + c1*v 12 + c2*v 17 + c3*v 31
    ac_rfl
compact_certificate theorem dot_44_2199023386624_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0] v = c0*v 17 + c1*v 41 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 17 + (c1*v 41) = c0*v 17 + c1*v 41
    ac_rfl
compact_certificate theorem dot_44_268468288_case1 (c0 c1 c2 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 15 + c2*v 28 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 15 + (c2*v 28)) = c0*v 6 + c1*v 15 + c2*v 28
    ac_rfl
compact_certificate theorem dot_44_274911461376_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0] v = c0*v 25 + c1*v 38 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 25 + (c1*v 38) = c0*v 25 + c1*v 38
    ac_rfl
compact_certificate theorem dot_44_33554496_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 25) = c0*v 6 + c1*v 25
    ac_rfl
compact_certificate theorem dot_44_34359747072_case1 (c0 c1 c2 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0] v = c0*v 9 + c1*v 13 + c2*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 9 + (c1*v 13 + (c2*v 35)) = c0*v 9 + c1*v 13 + c2*v 35
    ac_rfl
compact_certificate theorem dot_44_34359869632_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 7 + c2*v 17 + c3*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 7 + (c2*v 17 + (c3*v 35))) = c0*v 6 + c1*v 7 + c2*v 17 + c3*v 35
    ac_rfl
compact_certificate theorem dot_44_36507353152_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,c3,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 + c2*v 31 + c3*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17 + (c2*v 31 + (c3*v 35))) = c0*v 6 + c1*v 17 + c2*v 31 + c3*v 35
    ac_rfl
compact_certificate theorem dot_44_393280_case1 (c0 c1 c2 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 + c2*v 18 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17 + (c2*v 18)) = c0*v 6 + c1*v 17 + c2*v 18
    ac_rfl
compact_certificate theorem dot_44_4194560_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 8 + c1*v 22 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 + (c1*v 22) = c0*v 8 + c1*v 22
    ac_rfl
compact_certificate theorem dot_44_4294968320_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 10 + c1*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 10 + (c1*v 32) = c0*v 10 + c1*v 32
    ac_rfl
compact_certificate theorem dot_44_4_case1 (c0 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 2 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 = c0*v 2
    ac_rfl
compact_certificate theorem dot_44_524352_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 19 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 19) = c0*v 6 + c1*v 19
    ac_rfl
compact_certificate theorem dot_44_536887296_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 14 + c1*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 14 + (c1*v 29) = c0*v 14 + c1*v 29
    ac_rfl
compact_certificate theorem dot_44_549789368320_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0] v = c0*v 25 + c1*v 39 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 25 + (c1*v 39) = c0*v 25 + c1*v 39
    ac_rfl
compact_certificate theorem dot_44_6442582080_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,c3,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 + c2*v 31 + c3*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17 + (c2*v 31 + (c3*v 32))) = c0*v 6 + c1*v 17 + c2*v 31 + c3*v 32
    ac_rfl
compact_certificate theorem dot_44_6597069766656_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,c1,0] v = c0*v 41 + c1*v 42 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 41 + (c1*v 42) = c0*v 41 + c1*v 42
    ac_rfl
compact_certificate theorem dot_44_67108928_case1 (c0 c1 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 26 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 26) = c0*v 6 + c1*v 26
    ac_rfl
compact_certificate theorem dot_44_68719477312_case1 (c0 c1 c2 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 9 + c2*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 9 + (c2*v 36)) = c0*v 6 + c1*v 9 + c2*v 36
    ac_rfl
compact_certificate theorem dot_44_70867091520_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,c3,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 + c2*v 31 + c3*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17 + (c2*v 31 + (c3*v 36))) = c0*v 6 + c1*v 17 + c2*v 31 + c3*v 36
    ac_rfl
compact_certificate theorem dot_44_8388608_case1 (c0 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 23 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 23 = c0*v 23
    ac_rfl
compact_certificate theorem dot_44_8589938752_case1 (c0 c1 c2 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 12 + c2*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 12 + (c2*v 33)) = c0*v 6 + c1*v 12 + c2*v 33
    ac_rfl
compact_certificate theorem dot_44_8796093022208_case1 (c0 : ℂ) (v : Fin 44→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0] v = c0*v 43 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 43 = c0*v 43
    ac_rfl

compact_certificate theorem dot_45_1048576_case1 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 20 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 20 = c0*v 20
    ac_rfl
compact_certificate theorem dot_45_1099511627780_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0] v = c0*v 2 + c1*v 40 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 40) = c0*v 2 + c1*v 40
    ac_rfl
compact_certificate theorem dot_45_1099578736640_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0] v = c0*v 26 + c1*v 40 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 26 + (c1*v 40) = c0*v 26 + c1*v 40
    ac_rfl
compact_certificate theorem dot_45_137438987264_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0] v = c0*v 10 + c1*v 15 + c2*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 10 + (c1*v 15 + (c2*v 37)) = c0*v 10 + c1*v 15 + c2*v 37
    ac_rfl
compact_certificate theorem dot_45_137573171232_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 27 + c2*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 27 + (c2*v 37)) = c0*v 5 + c1*v 27 + c2*v 37
    ac_rfl
compact_certificate theorem dot_45_141733953568_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,c3,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 15 + c2*v 32 + c3*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 15 + (c2*v 32 + (c3*v 37))) = c0*v 5 + c1*v 15 + c2*v 32 + c3*v 37
    ac_rfl
compact_certificate theorem dot_45_16777248_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 24 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 24) = c0*v 5 + c1*v 24
    ac_rfl
compact_certificate theorem dot_45_17179906048_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 15 + c2*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 15 + (c2*v 34)) = c0*v 12 + c1*v 15 + c2*v 34
    ac_rfl
compact_certificate theorem dot_45_17596481011712_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,c1] v = c0*v 32 + c1*v 44 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 32 + (c1*v 44) = c0*v 32 + c1*v 44
    ac_rfl
compact_certificate theorem dot_45_18253611136_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,c2,0,0,0,0,0,0,0,0,0,0] v = c0*v 7 + c1*v 30 + c2*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 30 + (c2*v 34)) = c0*v 7 + c1*v 30 + c2*v 34
    ac_rfl
compact_certificate theorem dot_45_1_case1 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 0 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 = c0*v 0
    ac_rfl
compact_certificate theorem dot_45_21474836512_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,c2,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 32 + c2*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 32 + (c2*v 34)) = c0*v 5 + c1*v 32 + c2*v 34
    ac_rfl
compact_certificate theorem dot_45_2147484192_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 9 + c2*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 9 + (c2*v 31)) = c0*v 5 + c1*v 9 + c2*v 31
    ac_rfl
compact_certificate theorem dot_45_2199023255552_case1 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0] v = c0*v 41 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 41 = c0*v 41
    ac_rfl
compact_certificate theorem dot_45_25165824_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 23 + c1*v 24 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 23 + (c1*v 24) = c0*v 23 + c1*v 24
    ac_rfl
compact_certificate theorem dot_45_262176_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 18 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 18) = c0*v 5 + c1*v 18
    ac_rfl
compact_certificate theorem dot_45_268451872_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 28 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 28)) = c0*v 5 + c1*v 14 + c2*v 28
    ac_rfl
compact_certificate theorem dot_45_268468256_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 15 + c2*v 28 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 15 + (c2*v 28)) = c0*v 5 + c1*v 15 + c2*v 28
    ac_rfl
compact_certificate theorem dot_45_274894684160_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0] v = c0*v 24 + c1*v 38 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 24 + (c1*v 38) = c0*v 24 + c1*v 38
    ac_rfl
compact_certificate theorem dot_45_2_case1 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 1 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 = c0*v 1
    ac_rfl
compact_certificate theorem dot_45_33587232_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 15 + c2*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 15 + (c2*v 25)) = c0*v 5 + c1*v 15 + c2*v 25
    ac_rfl
compact_certificate theorem dot_45_33927288716159_case1 (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![c0,c1,c2,c3,c4,c5,c6,0,c7,c8,0,c9,c10,c11,c12,c13,c14,0,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,0,0,c25,0,c26,c27,0,c28,c29,0,c30,c31,0,c32,c33,c34,c35] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 8 + c8*v 9 + c9*v 11 + c10*v 12 + c11*v 13 + c12*v 14 + c13*v 15 + c14*v 16 + c15*v 18 + c16*v 19 + c17*v 20 + c18*v 21 + c19*v 22 + c20*v 23 + c21*v 24 + c22*v 25 + c23*v 26 + c24*v 27 + c25*v 30 + c26*v 32 + c27*v 33 + c28*v 35 + c29*v 36 + c30*v 38 + c31*v 39 + c32*v 41 + c33*v 42 + c34*v 43 + c35*v 44 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 3 + (c4*v 4 + (c5*v 5 + (c6*v 6 + (c7*v 8 + (c8*v 9 + (c9*v 11 + (c10*v 12 + (c11*v 13 + (c12*v 14 + (c13*v 15 + (c14*v 16 + (c15*v 18 + (c16*v 19 + (c17*v 20 + (c18*v 21 + (c19*v 22 + (c20*v 23 + (c21*v 24 + (c22*v 25 + (c23*v 26 + (c24*v 27 + (c25*v 30 + (c26*v 32 + (c27*v 33 + (c28*v 35 + (c29*v 36 + (c30*v 38 + (c31*v 39 + (c32*v 41 + (c33*v 42 + (c34*v 43 + (c35*v 44))))))))))))))))))))))))))))))))))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 8 + c8*v 9 + c9*v 11 + c10*v 12 + c11*v 13 + c12*v 14 + c13*v 15 + c14*v 16 + c15*v 18 + c16*v 19 + c17*v 20 + c18*v 21 + c19*v 22 + c20*v 23 + c21*v 24 + c22*v 25 + c23*v 26 + c24*v 27 + c25*v 30 + c26*v 32 + c27*v 33 + c28*v 35 + c29*v 36 + c30*v 38 + c31*v 39 + c32*v 41 + c33*v 42 + c34*v 43 + c35*v 44
    ac_rfl
compact_certificate theorem dot_45_34359738624_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0] v = c0*v 8 + c1*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 + (c1*v 35) = c0*v 8 + c1*v 35
    ac_rfl
compact_certificate theorem dot_45_34361835520_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0] v = c0*v 21 + c1*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 21 + (c1*v 35) = c0*v 21 + c1*v 35
    ac_rfl
compact_certificate theorem dot_45_36507746304_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,c2,0,0,0,0,0,0,0,0,0] v = c0*v 19 + c1*v 31 + c2*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 19 + (c1*v 31 + (c2*v 35)) = c0*v 19 + c1*v 31 + c2*v 35
    ac_rfl
compact_certificate theorem dot_45_38654738464_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,c3,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 15 + c2*v 32 + c3*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 15 + (c2*v 32 + (c3*v 35))) = c0*v 5 + c1*v 15 + c2*v 32 + c3*v 35
    ac_rfl
compact_certificate theorem dot_45_4194304_case1 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 22 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 22 = c0*v 22
    ac_rfl
compact_certificate theorem dot_45_4294967456_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 7 + c2*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 7 + (c2*v 32)) = c0*v 5 + c1*v 7 + c2*v 32
    ac_rfl
compact_certificate theorem dot_45_4295002112_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 11 + c1*v 15 + c2*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 11 + (c1*v 15 + (c2*v 32)) = c0*v 11 + c1*v 15 + c2*v 32
    ac_rfl
compact_certificate theorem dot_45_4295131168_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 15 + c2*v 17 + c3*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 15 + (c2*v 17 + (c3*v 32))) = c0*v 5 + c1*v 15 + c2*v 17 + c3*v 32
    ac_rfl
compact_certificate theorem dot_45_4398046511360_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0] v = c0*v 8 + c1*v 42 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 + (c1*v 42) = c0*v 8 + c1*v 42
    ac_rfl
compact_certificate theorem dot_45_48_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 4 + c1*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 + (c1*v 5) = c0*v 4 + c1*v 5
    ac_rfl
compact_certificate theorem dot_45_536870976_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 29) = c0*v 6 + c1*v 29
    ac_rfl
compact_certificate theorem dot_45_536879104_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 13 + c1*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 13 + (c1*v 29) = c0*v 13 + c1*v 29
    ac_rfl
compact_certificate theorem dot_45_549755944992_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0] v = c0*v 5 + c1*v 17 + c2*v 39 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 17 + (c2*v 39)) = c0*v 5 + c1*v 17 + c2*v 39
    ac_rfl
compact_certificate theorem dot_45_6442450976_case1 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,c2,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 31 + c2*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 31 + (c2*v 32)) = c0*v 5 + c1*v 31 + c2*v 32
    ac_rfl
compact_certificate theorem dot_45_65568_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 16 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 16) = c0*v 5 + c1*v 16
    ac_rfl
compact_certificate theorem dot_45_67141632_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 15 + c1*v 26 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 15 + (c1*v 26) = c0*v 15 + c1*v 26
    ac_rfl
compact_certificate theorem dot_45_73014476832_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,c3,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 15 + c2*v 32 + c3*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 15 + (c2*v 32 + (c3*v 36))) = c0*v 5 + c1*v 15 + c2*v 32 + c3*v 36
    ac_rfl
compact_certificate theorem dot_45_8224_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 13 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 13) = c0*v 5 + c1*v 13
    ac_rfl
compact_certificate theorem dot_45_8589935616_case1 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 10 + c1*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 10 + (c1*v 33) = c0*v 10 + c1*v 33
    ac_rfl
compact_certificate theorem dot_45_8796093022208_case1 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0] v = c0*v 43 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 43 = c0*v 43
    ac_rfl
compact_certificate theorem dot_45_8_case1 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 3 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 = c0*v 3
    ac_rfl

compact_certificate theorem dot_78_10625324586456701730816_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,c1,0,0,0,0] v = c0*v 70 + c1*v 73 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 70 + (c1*v 73) = c0*v 70 + c1*v 73
    ac_rfl
compact_certificate theorem dot_78_108086391325331456_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 28 + c2*v 55 + c3*v 56 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 28 + (c2*v 55 + (c3*v 56))) = c0*v 12 + c1*v 28 + c2*v 55 + c3*v 56
    ac_rfl
compact_certificate theorem dot_78_1099511627776_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 40 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 40 = c0*v 40
    ac_rfl
compact_certificate theorem dot_78_1125899906846720_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 50 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 50) = c0*v 12 + c1*v 50
    ac_rfl
compact_certificate theorem dot_78_1152921504606847104_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 7 + c1*v 60 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 60) = c0*v 7 + c1*v 60
    ac_rfl
compact_certificate theorem dot_78_1152921504606912512_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 16 + c1*v 60 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 16 + (c1*v 60) = c0*v 16 + c1*v 60
    ac_rfl
compact_certificate theorem dot_78_1152921504615239680_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 23 + c2*v 60 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 23 + (c2*v 60)) = c0*v 12 + c1*v 23 + c2*v 60
    ac_rfl
compact_certificate theorem dot_78_1152923703630102528_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 41 + c1*v 60 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 41 + (c1*v 60) = c0*v 41 + c1*v 60
    ac_rfl
compact_certificate theorem dot_78_1152930300704063488_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 22 + c1*v 43 + c2*v 60 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 22 + (c1*v 43 + (c2*v 60)) = c0*v 22 + c1*v 43 + c2*v 60
    ac_rfl
compact_certificate theorem dot_78_1152991874424766464_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 30 + c1*v 46 + c2*v 60 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 30 + (c1*v 46 + (c2*v 60)) = c0*v 30 + c1*v 46 + c2*v 60
    ac_rfl
compact_certificate theorem dot_78_1157425104234221568_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 52 + c2*v 60 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 52 + (c2*v 60)) = c0*v 12 + c1*v 52 + c2*v 60
    ac_rfl
compact_certificate theorem dot_78_1180591620717679738880_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0] v = c0*v 28 + c1*v 70 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 28 + (c1*v 70) = c0*v 28 + c1*v 70
    ac_rfl
compact_certificate theorem dot_78_1188950301625817088_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 11 + c1*v 12 + c2*v 55 + c3*v 60 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 11 + (c1*v 12 + (c2*v 55 + (c3*v 60))) = c0*v 11 + c1*v 12 + c2*v 55 + c3*v 60
    ac_rfl
compact_certificate theorem dot_78_1188950301894250496_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 28 + c2*v 55 + c3*v 60 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 28 + (c2*v 55 + (c3*v 60))) = c0*v 12 + c1*v 28 + c2*v 55 + c3*v 60
    ac_rfl
compact_certificate theorem dot_78_137438953472_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 37 = c0*v 37
    ac_rfl
compact_certificate theorem dot_78_140737488359424_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 47 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 47) = c0*v 12 + c1*v 47
    ac_rfl
compact_certificate theorem dot_78_144115188077953024_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 21 + c1*v 57 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 21 + (c1*v 57) = c0*v 21 + c1*v 57
    ac_rfl
compact_certificate theorem dot_78_147576204389490098176_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0] v = c0*v 51 + c1*v 67 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 51 + (c1*v 67) = c0*v 51 + c1*v 67
    ac_rfl
compact_certificate theorem dot_78_151115727451828646838272_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0] v = c0*v 77 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 77 = c0*v 77
    ac_rfl
compact_certificate theorem dot_78_16_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 = c0*v 4
    ac_rfl
compact_certificate theorem dot_78_17181966336_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 21 + c1*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 21 + (c1*v 34) = c0*v 21 + c1*v 34
    ac_rfl
compact_certificate theorem dot_78_17592186044448_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 44 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 44) = c0*v 5 + c1*v 44
    ac_rfl
compact_certificate theorem dot_78_17592186048512_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 44 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 44) = c0*v 12 + c1*v 44
    ac_rfl
compact_certificate theorem dot_78_18014398778048512_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 17 + c1*v 28 + c2*v 54 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 17 + (c1*v 28 + (c2*v 54)) = c0*v 17 + c1*v 28 + c2*v 54
    ac_rfl
compact_certificate theorem dot_78_18446744073743106048_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 25 + c1*v 64 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 25 + (c1*v 64) = c0*v 25 + c1*v 64
    ac_rfl
compact_certificate theorem dot_78_18889465931478580854784_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0] v = c0*v 74 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 74 = c0*v 74
    ac_rfl
compact_certificate theorem dot_78_1_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 0 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 = c0*v 0
    ac_rfl
compact_certificate theorem dot_78_2097160_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 3 + c1*v 21 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 21) = c0*v 3 + c1*v 21
    ac_rfl
compact_certificate theorem dot_78_2251799847239680_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 25 + c1*v 51 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 25 + (c1*v 51) = c0*v 25 + c1*v 51
    ac_rfl
compact_certificate theorem dot_78_2305843009230602240_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 17 + c1*v 24 + c2*v 61 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 17 + (c1*v 24 + (c2*v 61)) = c0*v 17 + c1*v 24 + c2*v 61
    ac_rfl
compact_certificate theorem dot_78_2305843009482166272_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 15 + c2*v 28 + c3*v 61 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 15 + (c2*v 28 + (c3*v 61))) = c0*v 12 + c1*v 15 + c2*v 28 + c3*v 61
    ac_rfl
compact_certificate theorem dot_78_2341871806501097472_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 28 + c2*v 55 + c3*v 61 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 28 + (c2*v 55 + (c3*v 61))) = c0*v 12 + c1*v 28 + c2*v 55 + c3*v 61
    ac_rfl
compact_certificate theorem dot_78_2361183241434822610944_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0] v = c0*v 12 + c1*v 71 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 71) = c0*v 12 + c1*v 71
    ac_rfl
compact_certificate theorem dot_78_2415923200_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 28 + c2*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 28 + (c2*v 31)) = c0*v 12 + c1*v 28 + c2*v 31
    ac_rfl
compact_certificate theorem dot_78_256_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 = c0*v 8
    ac_rfl
compact_certificate theorem dot_78_268435968_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 9 + c1*v 28 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 9 + (c1*v 28) = c0*v 9 + c1*v 28
    ac_rfl
compact_certificate theorem dot_78_274877906944_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 38 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 38 = c0*v 38
    ac_rfl
compact_certificate theorem dot_78_281474976710720_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 48 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 48) = c0*v 6 + c1*v 48
    ac_rfl
compact_certificate theorem dot_78_281475245146112_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 28 + c1*v 48 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 28 + (c1*v 48) = c0*v 28 + c1*v 48
    ac_rfl
compact_certificate theorem dot_78_295147922771538870272_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0] v = c0*v 44 + c1*v 68 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 44 + (c1*v 68) = c0*v 44 + c1*v 68
    ac_rfl
compact_certificate theorem dot_78_2_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 1 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 = c0*v 1
    ac_rfl
compact_certificate theorem dot_78_301048485100861649715199_case1 (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 c53 c54 c55 c56 c57 c58 c59 c60 c61 c62 c63 c64 c65 c66 c67 c68 c69 c70 c71 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,0,c17,c18,c19,c20,0,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,0,c46,c47,c48,c49,c50,c51,c52,0,c53,c54,c55,c56,0,c57,c58,c59,c60,c61,c62,c63,c64,0,c65,c66,c67,c68,c69,c70,c71] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 7 + c8*v 8 + c9*v 9 + c10*v 10 + c11*v 11 + c12*v 12 + c13*v 13 + c14*v 14 + c15*v 15 + c16*v 16 + c17*v 18 + c18*v 19 + c19*v 20 + c20*v 21 + c21*v 23 + c22*v 24 + c23*v 25 + c24*v 26 + c25*v 27 + c26*v 28 + c27*v 29 + c28*v 30 + c29*v 31 + c30*v 32 + c31*v 33 + c32*v 34 + c33*v 35 + c34*v 36 + c35*v 37 + c36*v 38 + c37*v 39 + c38*v 40 + c39*v 41 + c40*v 42 + c41*v 43 + c42*v 44 + c43*v 45 + c44*v 46 + c45*v 47 + c46*v 49 + c47*v 50 + c48*v 51 + c49*v 52 + c50*v 53 + c51*v 54 + c52*v 55 + c53*v 57 + c54*v 58 + c55*v 59 + c56*v 60 + c57*v 62 + c58*v 63 + c59*v 64 + c60*v 65 + c61*v 66 + c62*v 67 + c63*v 68 + c64*v 69 + c65*v 71 + c66*v 72 + c67*v 73 + c68*v 74 + c69*v 75 + c70*v 76 + c71*v 77 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 3 + (c4*v 4 + (c5*v 5 + (c6*v 6 + (c7*v 7 + (c8*v 8 + (c9*v 9 + (c10*v 10 + (c11*v 11 + (c12*v 12 + (c13*v 13 + (c14*v 14 + (c15*v 15 + (c16*v 16 + (c17*v 18 + (c18*v 19 + (c19*v 20 + (c20*v 21 + (c21*v 23 + (c22*v 24 + (c23*v 25 + (c24*v 26 + (c25*v 27 + (c26*v 28 + (c27*v 29 + (c28*v 30 + (c29*v 31 + (c30*v 32 + (c31*v 33 + (c32*v 34 + (c33*v 35 + (c34*v 36 + (c35*v 37 + (c36*v 38 + (c37*v 39 + (c38*v 40 + (c39*v 41 + (c40*v 42 + (c41*v 43 + (c42*v 44 + (c43*v 45 + (c44*v 46 + (c45*v 47 + (c46*v 49 + (c47*v 50 + (c48*v 51 + (c49*v 52 + (c50*v 53 + (c51*v 54 + (c52*v 55 + (c53*v 57 + (c54*v 58 + (c55*v 59 + (c56*v 60 + (c57*v 62 + (c58*v 63 + (c59*v 64 + (c60*v 65 + (c61*v 66 + (c62*v 67 + (c63*v 68 + (c64*v 69 + (c65*v 71 + (c66*v 72 + (c67*v 73 + (c68*v 74 + (c69*v 75 + (c70*v 76 + (c71*v 77))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 7 + c8*v 8 + c9*v 9 + c10*v 10 + c11*v 11 + c12*v 12 + c13*v 13 + c14*v 14 + c15*v 15 + c16*v 16 + c17*v 18 + c18*v 19 + c19*v 20 + c20*v 21 + c21*v 23 + c22*v 24 + c23*v 25 + c24*v 26 + c25*v 27 + c26*v 28 + c27*v 29 + c28*v 30 + c29*v 31 + c30*v 32 + c31*v 33 + c32*v 34 + c33*v 35 + c34*v 36 + c35*v 37 + c36*v 38 + c37*v 39 + c38*v 40 + c39*v 41 + c40*v 42 + c41*v 43 + c42*v 44 + c43*v 45 + c44*v 46 + c45*v 47 + c46*v 49 + c47*v 50 + c48*v 51 + c49*v 52 + c50*v 53 + c51*v 54 + c52*v 55 + c53*v 57 + c54*v 58 + c55*v 59 + c56*v 60 + c57*v 62 + c58*v 63 + c59*v 64 + c60*v 65 + c61*v 66 + c62*v 67 + c63*v 68 + c64*v 69 + c65*v 71 + c66*v 72 + c67*v 73 + c68*v 74 + c69*v 75 + c70*v 76 + c71*v 77
    ac_rfl
compact_certificate theorem dot_78_324259173170679808_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 55 + c2*v 58 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 55 + (c2*v 58)) = c0*v 12 + c1*v 55 + c2*v 58
    ac_rfl
compact_certificate theorem dot_78_33558528_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 25) = c0*v 12 + c1*v 25
    ac_rfl
compact_certificate theorem dot_78_34359742464_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 35) = c0*v 12 + c1*v 35
    ac_rfl
compact_certificate theorem dot_78_35184372092928_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 45 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 45) = c0*v 12 + c1*v 45
    ac_rfl
compact_certificate theorem dot_78_36028797018976256_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 13 + c2*v 55 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 13 + (c2*v 55)) = c0*v 12 + c1*v 13 + c2*v 55
    ac_rfl
compact_certificate theorem dot_78_36028797018984448_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 14 + c2*v 55 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 14 + (c2*v 55)) = c0*v 12 + c1*v 14 + c2*v 55
    ac_rfl
compact_certificate theorem dot_78_36028797019226112_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 18 + c1*v 55 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 18 + (c1*v 55) = c0*v 18 + c1*v 55
    ac_rfl
compact_certificate theorem dot_78_36028797153185792_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 27 + c2*v 55 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 27 + (c2*v 55)) = c0*v 12 + c1*v 27 + c2*v 55
    ac_rfl
compact_certificate theorem dot_78_36028797287403520_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 28 + c2*v 55 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 28 + (c2*v 55)) = c0*v 12 + c1*v 28 + c2*v 55
    ac_rfl
compact_certificate theorem dot_78_36028797289496576_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 21 + c1*v 28 + c2*v 55 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 21 + (c1*v 28 + (c2*v 55)) = c0*v 21 + c1*v 28 + c2*v 55
    ac_rfl
compact_certificate theorem dot_78_36028797291597824_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 22 + c2*v 28 + c3*v 55 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 22 + (c2*v 28 + (c3*v 55))) = c0*v 12 + c1*v 22 + c2*v 28 + c3*v 55
    ac_rfl
compact_certificate theorem dot_78_36028798361145344_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 28 + c2*v 30 + c3*v 55 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 28 + (c2*v 30 + (c3*v 55))) = c0*v 12 + c1*v 28 + c2*v 30 + c3*v 55
    ac_rfl
compact_certificate theorem dot_78_36893505739605147648_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 44 + c1*v 65 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 44 + (c1*v 65) = c0*v 44 + c1*v 65
    ac_rfl
compact_certificate theorem dot_78_37778931862957161709568_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0] v = c0*v 75 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 75 = c0*v 75
    ac_rfl
compact_certificate theorem dot_78_4294971392_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 32) = c0*v 12 + c1*v 32
    ac_rfl
compact_certificate theorem dot_78_45035996273709056_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 53 + c2*v 55 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 53 + (c2*v 55)) = c0*v 12 + c1*v 53 + c2*v 55
    ac_rfl
compact_certificate theorem dot_78_4611686018427523072_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 17 + c2*v 62 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 17 + (c2*v 62)) = c0*v 12 + c1*v 17 + c2*v 62
    ac_rfl
compact_certificate theorem dot_78_4611686018696347648_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 19 + c1*v 28 + c2*v 62 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 19 + (c1*v 28 + (c2*v 62)) = c0*v 19 + c1*v 28 + c2*v 62
    ac_rfl
compact_certificate theorem dot_78_4611690416473899008_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 42 + c1*v 62 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 42 + (c1*v 62) = c0*v 42 + c1*v 62
    ac_rfl
compact_certificate theorem dot_78_4647714815714791424_case1 (c0 c1 c2 c3 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 28 + c2*v 55 + c3*v 62 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 28 + (c2*v 55 + (c3*v 62))) = c0*v 12 + c1*v 28 + c2*v 55 + c3*v 62
    ac_rfl
compact_certificate theorem dot_78_4722366482869645279232_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0] v = c0*v 16 + c1*v 72 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 16 + (c1*v 72) = c0*v 16 + c1*v 72
    ac_rfl
compact_certificate theorem dot_78_4_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 2 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 = c0*v 2
    ac_rfl
compact_certificate theorem dot_78_536871936_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 10 + c1*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 10 + (c1*v 29) = c0*v 10 + c1*v 29
    ac_rfl
compact_certificate theorem dot_78_536875008_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 29) = c0*v 12 + c1*v 29
    ac_rfl
compact_certificate theorem dot_78_549755879424_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 16 + c1*v 39 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 16 + (c1*v 39) = c0*v 16 + c1*v 39
    ac_rfl
compact_certificate theorem dot_78_562950221860864_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 28 + c2*v 49 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 28 + (c2*v 49)) = c0*v 12 + c1*v 28 + c2*v 49
    ac_rfl
compact_certificate theorem dot_78_576460752307621888_case1 (c0 c1 c2 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 22 + c2*v 59 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 22 + (c2*v 59)) = c0*v 12 + c1*v 22 + c2*v 59
    ac_rfl
compact_certificate theorem dot_78_590295810358705651712_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0] v = c0*v 69 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 69 = c0*v 69
    ac_rfl
compact_certificate theorem dot_78_67112960_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 26 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 26) = c0*v 12 + c1*v 26
    ac_rfl
compact_certificate theorem dot_78_68719476736_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 36 = c0*v 36
    ac_rfl
compact_certificate theorem dot_78_72057594038976512_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 20 + c1*v 56 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 20 + (c1*v 56) = c0*v 20 + c1*v 56
    ac_rfl
compact_certificate theorem dot_78_73787257769814917120_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 48 + c1*v 66 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 48 + (c1*v 66) = c0*v 48 + c1*v 66
    ac_rfl
compact_certificate theorem dot_78_75557863725914323419136_case1 (c0 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0] v = c0*v 76 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 76 = c0*v 76
    ac_rfl
compact_certificate theorem dot_78_8590000128_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 16 + c1*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 16 + (c1*v 33) = c0*v 16 + c1*v 33
    ac_rfl
compact_certificate theorem dot_78_9223372036854779904_case1 (c0 c1 : ℂ) (v : Fin 78→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 63 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 63) = c0*v 12 + c1*v 63
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end
end

/-! ## QuantitativeArithmeticSparseDotEvaluationIndexMaskBundleSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_10_105 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,c3,0,0,0] v = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5 + (c3*v 6))) = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 6
    ac_rfl

theorem dot_10_114 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,c0,0,0,c1,c2,c3,0,0,0] v = c0*v 1 + c1*v 4 + c2*v 5 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4 + (c2*v 5 + (c3*v 6))) = c0*v 1 + c1*v 4 + c2*v 5 + c3*v 6
    ac_rfl

theorem dot_10_132 (c0 c1 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,c1,0,0] v = c0*v 2 + c1*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 7) = c0*v 2 + c1*v 7
    ac_rfl

theorem dot_10_145 (c0 c1 c2 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,0,0,0,c1,0,0,c2,0,0] v = c0*v 0 + c1*v 4 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 4 + (c2*v 7)) = c0*v 0 + c1*v 4 + c2*v 7
    ac_rfl

theorem dot_10_164 (c0 c1 c2 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,c0,0,0,c1,0,c2,0,0] v = c0*v 2 + c1*v 5 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 5 + (c2*v 7)) = c0*v 2 + c1*v 5 + c2*v 7
    ac_rfl

theorem dot_10_169 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,0,c3,0,0] v = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5 + (c3*v 7))) = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 7
    ac_rfl

theorem dot_10_180 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,c0,0,c1,c2,0,c3,0,0] v = c0*v 2 + c1*v 4 + c2*v 5 + c3*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 5 + (c3*v 7))) = c0*v 2 + c1*v 4 + c2*v 5 + c3*v 7
    ac_rfl

theorem dot_10_18 (c0 c1 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,0,0,0,0] v = c0*v 1 + c1*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4) = c0*v 1 + c1*v 4
    ac_rfl

theorem dot_10_1 (c0 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0,0] v = c0*v 0 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 = c0*v 0
    ac_rfl

theorem dot_10_257 (c0 c1 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,c1,0] v = c0*v 0 + c1*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 8) = c0*v 0 + c1*v 8
    ac_rfl

theorem dot_10_259 (c0 c1 c2 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,c1,0,0,0,0,0,0,c2,0] v = c0*v 0 + c1*v 1 + c2*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 8)) = c0*v 0 + c1*v 1 + c2*v 8
    ac_rfl

theorem dot_10_266 (c0 c1 c2 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,c0,0,c1,0,0,0,0,c2,0] v = c0*v 1 + c1*v 3 + c2*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 8)) = c0*v 1 + c1*v 3 + c2*v 8
    ac_rfl

theorem dot_10_283 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,c1,0,c2,c3,0,0,0,c4,0] v = c0*v 0 + c1*v 1 + c2*v 3 + c3*v 4 + c4*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 3 + (c3*v 4 + (c4*v 8)))) = c0*v 0 + c1*v 1 + c2*v 3 + c3*v 4 + c4*v 8
    ac_rfl

theorem dot_10_297 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,0,0,c3,0] v = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5 + (c3*v 8))) = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 8
    ac_rfl

theorem dot_10_298 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,c0,0,c1,0,c2,0,0,c3,0] v = c0*v 1 + c1*v 3 + c2*v 5 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 5 + (c3*v 8))) = c0*v 1 + c1*v 3 + c2*v 5 + c3*v 8
    ac_rfl

theorem dot_10_338 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,c2,0,c3,0] v = c0*v 1 + c1*v 4 + c2*v 6 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4 + (c2*v 6 + (c3*v 8))) = c0*v 1 + c1*v 4 + c2*v 6 + c3*v 8
    ac_rfl

theorem dot_10_339 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,c1,0,0,c2,0,c3,0,c4,0] v = c0*v 0 + c1*v 1 + c2*v 4 + c3*v 6 + c4*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 4 + (c3*v 6 + (c4*v 8)))) = c0*v 0 + c1*v 1 + c2*v 4 + c3*v 6 + c4*v 8
    ac_rfl

theorem dot_10_340 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,c0,0,c1,0,c2,0,c3,0] v = c0*v 2 + c1*v 4 + c2*v 6 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 6 + (c3*v 8))) = c0*v 2 + c1*v 4 + c2*v 6 + c3*v 8
    ac_rfl

theorem dot_10_41 (c0 c1 c2 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,0,0,0,0] v = c0*v 0 + c1*v 3 + c2*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5)) = c0*v 0 + c1*v 3 + c2*v 5
    ac_rfl

theorem dot_10_420 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,c0,0,0,c1,0,c2,c3,0] v = c0*v 2 + c1*v 5 + c2*v 7 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 5 + (c2*v 7 + (c3*v 8))) = c0*v 2 + c1*v 5 + c2*v 7 + c3*v 8
    ac_rfl

theorem dot_10_45 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,0,c1,c2,0,c3,0,0,0,0] v = c0*v 0 + c1*v 2 + c2*v 3 + c3*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 3 + (c3*v 5))) = c0*v 0 + c1*v 2 + c2*v 3 + c3*v 5
    ac_rfl

theorem dot_10_520 (c0 c1 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,c1] v = c0*v 3 + c1*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 9) = c0*v 3 + c1*v 9
    ac_rfl

theorem dot_10_52 (c0 c1 c2 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,c0,0,c1,c2,0,0,0,0] v = c0*v 2 + c1*v 4 + c2*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 5)) = c0*v 2 + c1*v 4 + c2*v 5
    ac_rfl

theorem dot_10_553 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,0,0,0,c3] v = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5 + (c3*v 9))) = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 9
    ac_rfl

theorem dot_10_554 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,c0,0,c1,0,c2,0,0,0,c3] v = c0*v 1 + c1*v 3 + c2*v 5 + c3*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 5 + (c3*v 9))) = c0*v 1 + c1*v 3 + c2*v 5 + c3*v 9
    ac_rfl

theorem dot_10_576 (c0 c1 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,c1] v = c0*v 6 + c1*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 9) = c0*v 6 + c1*v 9
    ac_rfl

theorem dot_10_596 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,c0,0,c1,0,c2,0,0,c3] v = c0*v 2 + c1*v 4 + c2*v 6 + c3*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 6 + (c3*v 9))) = c0*v 2 + c1*v 4 + c2*v 6 + c3*v 9
    ac_rfl

theorem dot_10_641 (c0 c1 c2 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,c1,0,c2] v = c0*v 0 + c1*v 7 + c2*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 7 + (c2*v 9)) = c0*v 0 + c1*v 7 + c2*v 9
    ac_rfl

theorem dot_10_66 (c0 c1 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,c0,0,0,0,0,c1,0,0,0] v = c0*v 1 + c1*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 6) = c0*v 1 + c1*v 6
    ac_rfl

theorem dot_10_672 (c0 c1 c2 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,c1,0,c2] v = c0*v 5 + c1*v 7 + c2*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 7 + (c2*v 9)) = c0*v 5 + c1*v 7 + c2*v 9
    ac_rfl

theorem dot_10_676 (c0 c1 c2 c3 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,c0,0,0,c1,0,c2,0,c3] v = c0*v 2 + c1*v 5 + c2*v 7 + c3*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 5 + (c2*v 7 + (c3*v 9))) = c0*v 2 + c1*v 5 + c2*v 7 + c3*v 9
    ac_rfl

theorem dot_10_681 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,0,c3,0,c4] v = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 7 + c4*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5 + (c3*v 7 + (c4*v 9)))) = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 7 + c4*v 9
    ac_rfl

theorem dot_10_68 (c0 c1 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,c0,0,0,0,c1,0,0,0] v = c0*v 2 + c1*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 6) = c0*v 2 + c1*v 6
    ac_rfl

theorem dot_10_6 (c0 c1 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,c0,c1,0,0,0,0,0,0,0] v = c0*v 1 + c1*v 2 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 2) = c0*v 1 + c1*v 2
    ac_rfl

theorem dot_10_72 (c0 c1 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,0,c0,0,0,c1,0,0,0] v = c0*v 3 + c1*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 6) = c0*v 3 + c1*v 6
    ac_rfl

theorem dot_10_82 (c0 c1 c2 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,c2,0,0,0] v = c0*v 1 + c1*v 4 + c2*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4 + (c2*v 6)) = c0*v 1 + c1*v 4 + c2*v 6
    ac_rfl

theorem dot_10_84 (c0 c1 c2 : ℂ) (v : Fin 10→ℂ) :
    dotProduct ![0,0,c0,0,c1,0,c2,0,0,0] v = c0*v 2 + c1*v 4 + c2*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 6)) = c0*v 2 + c1*v 4 + c2*v 6
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_11_1024 (c0 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,c0] v = c0*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 10 = c0*v 10
    ac_rfl

theorem dot_11_1025 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0,0,c1] v = c0*v 0 + c1*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 10) = c0*v 0 + c1*v 10
    ac_rfl

theorem dot_11_1088 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,c1] v = c0*v 6 + c1*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 10) = c0*v 6 + c1*v 10
    ac_rfl

theorem dot_11_1129 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,c3,0,0,0,c4] v = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 6 + c4*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5 + (c3*v 6 + (c4*v 10)))) = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 6 + c4*v 10
    ac_rfl

theorem dot_11_1172 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,c0,0,c1,0,0,c2,0,0,c3] v = c0*v 2 + c1*v 4 + c2*v 7 + c3*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 7 + (c3*v 10))) = c0*v 2 + c1*v 4 + c2*v 7 + c3*v 10
    ac_rfl

theorem dot_11_1176 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,0,c0,c1,0,0,c2,0,0,c3] v = c0*v 3 + c1*v 4 + c2*v 7 + c3*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 4 + (c2*v 7 + (c3*v 10))) = c0*v 3 + c1*v 4 + c2*v 7 + c3*v 10
    ac_rfl

theorem dot_11_1298 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,0,0,c2,0,c3] v = c0*v 1 + c1*v 4 + c2*v 8 + c3*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4 + (c2*v 8 + (c3*v 10))) = c0*v 1 + c1*v 4 + c2*v 8 + c3*v 10
    ac_rfl

theorem dot_11_130 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,c1,0,0,0] v = c0*v 1 + c1*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 7) = c0*v 1 + c1*v 7
    ac_rfl

theorem dot_11_1322 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,c1,0,c2,0,0,c3,0,c4] v = c0*v 1 + c1*v 3 + c2*v 5 + c3*v 8 + c4*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 5 + (c3*v 8 + (c4*v 10)))) = c0*v 1 + c1*v 3 + c2*v 5 + c3*v 8 + c4*v 10
    ac_rfl

theorem dot_11_144 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,0,0,c0,0,0,c1,0,0,0] v = c0*v 4 + c1*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 + (c1*v 7) = c0*v 4 + c1*v 7
    ac_rfl

theorem dot_11_148 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,c0,0,c1,0,0,c2,0,0,0] v = c0*v 2 + c1*v 4 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 7)) = c0*v 2 + c1*v 4 + c2*v 7
    ac_rfl

theorem dot_11_1586 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,0,c1,c2,0,0,0,c3,c4] v = c0*v 1 + c1*v 4 + c2*v 5 + c3*v 9 + c4*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4 + (c2*v 5 + (c3*v 9 + (c4*v 10)))) = c0*v 1 + c1*v 4 + c2*v 5 + c3*v 9 + c4*v 10
    ac_rfl

theorem dot_11_1684 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,c0,0,c1,0,0,c2,0,c3,c4] v = c0*v 2 + c1*v 4 + c2*v 7 + c3*v 9 + c4*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 7 + (c3*v 9 + (c4*v 10)))) = c0*v 2 + c1*v 4 + c2*v 7 + c3*v 9 + c4*v 10
    ac_rfl

theorem dot_11_168 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,0,c0,0,c1,0,c2,0,0,0] v = c0*v 3 + c1*v 5 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 5 + (c2*v 7)) = c0*v 3 + c1*v 5 + c2*v 7
    ac_rfl

theorem dot_11_17 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,0,0,c1,0,0,0,0,0,0] v = c0*v 0 + c1*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 4) = c0*v 0 + c1*v 4
    ac_rfl

theorem dot_11_194 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,0,0,0,c1,c2,0,0,0] v = c0*v 1 + c1*v 6 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 6 + (c2*v 7)) = c0*v 1 + c1*v 6 + c2*v 7
    ac_rfl

theorem dot_11_197 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,c1,0,0,0,c2,c3,0,0,0] v = c0*v 0 + c1*v 2 + c2*v 6 + c3*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 6 + (c3*v 7))) = c0*v 0 + c1*v 2 + c2*v 6 + c3*v 7
    ac_rfl

theorem dot_11_209 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,0,0,c1,0,c2,c3,0,0,0] v = c0*v 0 + c1*v 4 + c2*v 6 + c3*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 4 + (c2*v 6 + (c3*v 7))) = c0*v 0 + c1*v 4 + c2*v 6 + c3*v 7
    ac_rfl

theorem dot_11_24 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,0,c0,c1,0,0,0,0,0,0] v = c0*v 3 + c1*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 4) = c0*v 3 + c1*v 4
    ac_rfl

theorem dot_11_257 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,c1,0,0] v = c0*v 0 + c1*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 8) = c0*v 0 + c1*v 8
    ac_rfl

theorem dot_11_258 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,c1,0,0] v = c0*v 1 + c1*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 8) = c0*v 1 + c1*v 8
    ac_rfl

theorem dot_11_260 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,c1,0,0] v = c0*v 2 + c1*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 8) = c0*v 2 + c1*v 8
    ac_rfl

theorem dot_11_262 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,c1,0,0,0,0,0,c2,0,0] v = c0*v 1 + c1*v 2 + c2*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 2 + (c2*v 8)) = c0*v 1 + c1*v 2 + c2*v 8
    ac_rfl

theorem dot_11_26 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,c1,c2,0,0,0,0,0,0] v = c0*v 1 + c1*v 3 + c2*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 4)) = c0*v 1 + c1*v 3 + c2*v 4
    ac_rfl

theorem dot_11_274 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,0,0,c2,0,0] v = c0*v 1 + c1*v 4 + c2*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4 + (c2*v 8)) = c0*v 1 + c1*v 4 + c2*v 8
    ac_rfl

theorem dot_11_297 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,0,0,c3,0,0] v = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5 + (c3*v 8))) = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 8
    ac_rfl

theorem dot_11_325 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,c1,0,0,0,c2,0,c3,0,0] v = c0*v 0 + c1*v 2 + c2*v 6 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 6 + (c3*v 8))) = c0*v 0 + c1*v 2 + c2*v 6 + c3*v 8
    ac_rfl

theorem dot_11_330 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,c1,0,0,c2,0,c3,0,0] v = c0*v 1 + c1*v 3 + c2*v 6 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 6 + (c3*v 8))) = c0*v 1 + c1*v 3 + c2*v 6 + c3*v 8
    ac_rfl

theorem dot_11_34 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,0,0,c1,0,0,0,0,0] v = c0*v 1 + c1*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 5) = c0*v 1 + c1*v 5
    ac_rfl

theorem dot_11_36 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,c0,0,0,c1,0,0,0,0,0] v = c0*v 2 + c1*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 5) = c0*v 2 + c1*v 5
    ac_rfl

theorem dot_11_387 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,c1,0,0,0,0,0,c2,c3,0,0] v = c0*v 0 + c1*v 1 + c2*v 7 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 7 + (c3*v 8))) = c0*v 0 + c1*v 1 + c2*v 7 + c3*v 8
    ac_rfl

theorem dot_11_402 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,0,c2,c3,0,0] v = c0*v 1 + c1*v 4 + c2*v 7 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4 + (c2*v 7 + (c3*v 8))) = c0*v 1 + c1*v 4 + c2*v 7 + c3*v 8
    ac_rfl

theorem dot_11_404 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,c0,0,c1,0,0,c2,c3,0,0] v = c0*v 2 + c1*v 4 + c2*v 7 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 7 + (c3*v 8))) = c0*v 2 + c1*v 4 + c2*v 7 + c3*v 8
    ac_rfl

theorem dot_11_41 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,0,0,0,0,0] v = c0*v 0 + c1*v 3 + c2*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5)) = c0*v 0 + c1*v 3 + c2*v 5
    ac_rfl

theorem dot_11_516 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,c1,0] v = c0*v 2 + c1*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 9) = c0*v 2 + c1*v 9
    ac_rfl

theorem dot_11_521 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,0,c1,0,0,0,0,0,c2,0] v = c0*v 0 + c1*v 3 + c2*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 9)) = c0*v 0 + c1*v 3 + c2*v 9
    ac_rfl

theorem dot_11_544 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,c1,0] v = c0*v 5 + c1*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 9) = c0*v 5 + c1*v 9
    ac_rfl

theorem dot_11_576 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,c1,0] v = c0*v 6 + c1*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 9) = c0*v 6 + c1*v 9
    ac_rfl

theorem dot_11_593 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,0,0,c1,0,c2,0,0,c3,0] v = c0*v 0 + c1*v 4 + c2*v 6 + c3*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 4 + (c2*v 6 + (c3*v 9))) = c0*v 0 + c1*v 4 + c2*v 6 + c3*v 9
    ac_rfl

theorem dot_11_5 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,c1,0,0,0,0,0,0,0,0] v = c0*v 0 + c1*v 2 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2) = c0*v 0 + c1*v 2
    ac_rfl

theorem dot_11_617 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,c3,0,0,c4,0] v = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 6 + c4*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5 + (c3*v 6 + (c4*v 9)))) = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 6 + c4*v 9
    ac_rfl

theorem dot_11_641 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,c1,0,c2,0] v = c0*v 0 + c1*v 7 + c2*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 7 + (c2*v 9)) = c0*v 0 + c1*v 7 + c2*v 9
    ac_rfl

theorem dot_11_660 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,c0,0,c1,0,0,c2,0,c3,0] v = c0*v 2 + c1*v 4 + c2*v 7 + c3*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 7 + (c3*v 9))) = c0*v 2 + c1*v 4 + c2*v 7 + c3*v 9
    ac_rfl

theorem dot_11_68 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,c0,0,0,0,c1,0,0,0,0] v = c0*v 2 + c1*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 6) = c0*v 2 + c1*v 6
    ac_rfl

theorem dot_11_69 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,c1,0,0,0,c2,0,0,0,0] v = c0*v 0 + c1*v 2 + c2*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 6)) = c0*v 0 + c1*v 2 + c2*v 6
    ac_rfl

theorem dot_11_71 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,c1,c2,0,0,0,c3,0,0,0,0] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 6))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 6
    ac_rfl

theorem dot_11_74 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,c1,0,0,c2,0,0,0,0] v = c0*v 1 + c1*v 3 + c2*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 6)) = c0*v 1 + c1*v 3 + c2*v 6
    ac_rfl

theorem dot_11_786 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,0,0,c2,c3,0] v = c0*v 1 + c1*v 4 + c2*v 8 + c3*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4 + (c2*v 8 + (c3*v 9))) = c0*v 1 + c1*v 4 + c2*v 8 + c3*v 9
    ac_rfl

theorem dot_11_78 (c0 c1 c2 c3 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,c0,c1,c2,0,0,c3,0,0,0,0] v = c0*v 1 + c1*v 2 + c2*v 3 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 2 + (c2*v 3 + (c3*v 6))) = c0*v 1 + c1*v 2 + c2*v 3 + c3*v 6
    ac_rfl

theorem dot_11_80 (c0 c1 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,0,0,c0,0,c1,0,0,0,0] v = c0*v 4 + c1*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 + (c1*v 6) = c0*v 4 + c1*v 6
    ac_rfl

theorem dot_11_84 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![0,0,c0,0,c1,0,c2,0,0,0,0] v = c0*v 2 + c1*v 4 + c2*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 6)) = c0*v 2 + c1*v 4 + c2*v 6
    ac_rfl

theorem dot_11_97 (c0 c1 c2 : ℂ) (v : Fin 11→ℂ) :
    dotProduct ![c0,0,0,0,0,c1,c2,0,0,0,0] v = c0*v 0 + c1*v 5 + c2*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 5 + (c2*v 6)) = c0*v 0 + c1*v 5 + c2*v 6
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_12_1028 (c0 c1 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,c1,0] v = c0*v 2 + c1*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 10) = c0*v 2 + c1*v 10
    ac_rfl

theorem dot_12_1032 (c0 c1 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,0,c1,0] v = c0*v 3 + c1*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 10) = c0*v 3 + c1*v 10
    ac_rfl

theorem dot_12_1096 (c0 c1 c2 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,0,c0,0,0,c1,0,0,0,c2,0] v = c0*v 3 + c1*v 6 + c2*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 6 + (c2*v 10)) = c0*v 3 + c1*v 6 + c2*v 10
    ac_rfl

theorem dot_12_1122 (c0 c1 c2 c3 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,c0,0,0,0,c1,c2,0,0,0,c3,0] v = c0*v 1 + c1*v 5 + c2*v 6 + c3*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 5 + (c2*v 6 + (c3*v 10))) = c0*v 1 + c1*v 5 + c2*v 6 + c3*v 10
    ac_rfl

theorem dot_12_1170 (c0 c1 c2 c3 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,0,c2,0,0,c3,0] v = c0*v 1 + c1*v 4 + c2*v 7 + c3*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4 + (c2*v 7 + (c3*v 10))) = c0*v 1 + c1*v 4 + c2*v 7 + c3*v 10
    ac_rfl

theorem dot_12_1282 (c0 c1 c2 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,c1,0,c2,0] v = c0*v 1 + c1*v 8 + c2*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 8 + (c2*v 10)) = c0*v 1 + c1*v 8 + c2*v 10
    ac_rfl

theorem dot_12_130 (c0 c1 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,c1,0,0,0,0] v = c0*v 1 + c1*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 7) = c0*v 1 + c1*v 7
    ac_rfl

theorem dot_12_1320 (c0 c1 c2 c3 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,0,c0,0,c1,0,0,c2,0,c3,0] v = c0*v 3 + c1*v 5 + c2*v 8 + c3*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 5 + (c2*v 8 + (c3*v 10))) = c0*v 3 + c1*v 5 + c2*v 8 + c3*v 10
    ac_rfl

theorem dot_12_132 (c0 c1 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,c1,0,0,0,0] v = c0*v 2 + c1*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 7) = c0*v 2 + c1*v 7
    ac_rfl

theorem dot_12_146 (c0 c1 c2 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,0,c2,0,0,0,0] v = c0*v 1 + c1*v 4 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4 + (c2*v 7)) = c0*v 1 + c1*v 4 + c2*v 7
    ac_rfl

theorem dot_12_17 (c0 c1 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![c0,0,0,0,c1,0,0,0,0,0,0,0] v = c0*v 0 + c1*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 4) = c0*v 0 + c1*v 4
    ac_rfl

theorem dot_12_18 (c0 c1 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,0,0,0,0,0,0] v = c0*v 1 + c1*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4) = c0*v 1 + c1*v 4
    ac_rfl

theorem dot_12_201 (c0 c1 c2 c3 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![c0,0,0,c1,0,0,c2,c3,0,0,0,0] v = c0*v 0 + c1*v 3 + c2*v 6 + c3*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 6 + (c3*v 7))) = c0*v 0 + c1*v 3 + c2*v 6 + c3*v 7
    ac_rfl

theorem dot_12_2052 (c0 c1 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,0,c1] v = c0*v 2 + c1*v 11 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 11) = c0*v 2 + c1*v 11
    ac_rfl

theorem dot_12_2060 (c0 c1 c2 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,c0,c1,0,0,0,0,0,0,0,c2] v = c0*v 2 + c1*v 3 + c2*v 11 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 3 + (c2*v 11)) = c0*v 2 + c1*v 3 + c2*v 11
    ac_rfl

theorem dot_12_210 (c0 c1 c2 c3 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,c2,c3,0,0,0,0] v = c0*v 1 + c1*v 4 + c2*v 6 + c3*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4 + (c2*v 6 + (c3*v 7))) = c0*v 1 + c1*v 4 + c2*v 6 + c3*v 7
    ac_rfl

theorem dot_12_2344 (c0 c1 c2 c3 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,0,c0,0,c1,0,0,c2,0,0,c3] v = c0*v 3 + c1*v 5 + c2*v 8 + c3*v 11 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 5 + (c2*v 8 + (c3*v 11))) = c0*v 3 + c1*v 5 + c2*v 8 + c3*v 11
    ac_rfl

theorem dot_12_2345 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,0,0,c3,0,0,c4] v = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 8 + c4*v 11 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5 + (c3*v 8 + (c4*v 11)))) = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 8 + c4*v 11
    ac_rfl

theorem dot_12_2356 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,c0,0,c1,c2,0,0,c3,0,0,c4] v = c0*v 2 + c1*v 4 + c2*v 5 + c3*v 8 + c4*v 11 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 5 + (c3*v 8 + (c4*v 11)))) = c0*v 2 + c1*v 4 + c2*v 5 + c3*v 8 + c4*v 11
    ac_rfl

theorem dot_12_2568 (c0 c1 c2 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,c1,0,c2] v = c0*v 3 + c1*v 9 + c2*v 11 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 9 + (c2*v 11)) = c0*v 3 + c1*v 9 + c2*v 11
    ac_rfl

theorem dot_12_296 (c0 c1 c2 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,0,c0,0,c1,0,0,c2,0,0,0] v = c0*v 3 + c1*v 5 + c2*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 5 + (c2*v 8)) = c0*v 3 + c1*v 5 + c2*v 8
    ac_rfl

theorem dot_12_304 (c0 c1 c2 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,0,0,c0,c1,0,0,c2,0,0,0] v = c0*v 4 + c1*v 5 + c2*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 + (c1*v 5 + (c2*v 8)) = c0*v 4 + c1*v 5 + c2*v 8
    ac_rfl

theorem dot_12_3072 (c0 c1 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,c0,c1] v = c0*v 10 + c1*v 11 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 10 + (c1*v 11) = c0*v 10 + c1*v 11
    ac_rfl

theorem dot_12_329 (c0 c1 c2 c3 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![c0,0,0,c1,0,0,c2,0,c3,0,0,0] v = c0*v 0 + c1*v 3 + c2*v 6 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 6 + (c3*v 8))) = c0*v 0 + c1*v 3 + c2*v 6 + c3*v 8
    ac_rfl

theorem dot_12_34 (c0 c1 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,c0,0,0,0,c1,0,0,0,0,0,0] v = c0*v 1 + c1*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 5) = c0*v 1 + c1*v 5
    ac_rfl

theorem dot_12_520 (c0 c1 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,c1,0,0] v = c0*v 3 + c1*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 9) = c0*v 3 + c1*v 9
    ac_rfl

theorem dot_12_544 (c0 c1 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,c1,0,0] v = c0*v 5 + c1*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 9) = c0*v 5 + c1*v 9
    ac_rfl

theorem dot_12_641 (c0 c1 c2 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,c1,0,c2,0,0] v = c0*v 0 + c1*v 7 + c2*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 7 + (c2*v 9)) = c0*v 0 + c1*v 7 + c2*v 9
    ac_rfl

theorem dot_12_656 (c0 c1 c2 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![0,0,0,0,c0,0,0,c1,0,c2,0,0] v = c0*v 4 + c1*v 7 + c2*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 + (c1*v 7 + (c2*v 9)) = c0*v 4 + c1*v 7 + c2*v 9
    ac_rfl

theorem dot_12_707 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![c0,c1,0,0,0,0,c2,c3,0,c4,0,0] v = c0*v 0 + c1*v 1 + c2*v 6 + c3*v 7 + c4*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 6 + (c3*v 7 + (c4*v 9)))) = c0*v 0 + c1*v 1 + c2*v 6 + c3*v 7 + c4*v 9
    ac_rfl

theorem dot_12_73 (c0 c1 c2 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![c0,0,0,c1,0,0,c2,0,0,0,0,0] v = c0*v 0 + c1*v 3 + c2*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 6)) = c0*v 0 + c1*v 3 + c2*v 6
    ac_rfl

theorem dot_12_77 (c0 c1 c2 c3 : ℂ) (v : Fin 12→ℂ) :
    dotProduct ![c0,0,c1,c2,0,0,c3,0,0,0,0,0] v = c0*v 0 + c1*v 2 + c2*v 3 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 3 + (c3*v 6))) = c0*v 0 + c1*v 2 + c2*v 3 + c3*v 6
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_13_1040 (c0 c1 : ℂ) (v : Fin 13→ℂ) :
    dotProduct ![0,0,0,0,c0,0,0,0,0,0,c1,0,0] v = c0*v 4 + c1*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 + (c1*v 10) = c0*v 4 + c1*v 10
    ac_rfl

theorem dot_13_1281 (c0 c1 c2 : ℂ) (v : Fin 13→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,c1,0,c2,0,0] v = c0*v 0 + c1*v 8 + c2*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 8 + (c2*v 10)) = c0*v 0 + c1*v 8 + c2*v 10
    ac_rfl

theorem dot_13_200 (c0 c1 c2 : ℂ) (v : Fin 13→ℂ) :
    dotProduct ![0,0,0,c0,0,0,c1,c2,0,0,0,0,0] v = c0*v 3 + c1*v 6 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 6 + (c2*v 7)) = c0*v 3 + c1*v 6 + c2*v 7
    ac_rfl

theorem dot_13_2112 (c0 c1 : ℂ) (v : Fin 13→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,c1,0] v = c0*v 6 + c1*v 11 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 11) = c0*v 6 + c1*v 11
    ac_rfl

theorem dot_13_261 (c0 c1 c2 : ℂ) (v : Fin 13→ℂ) :
    dotProduct ![c0,0,c1,0,0,0,0,0,c2,0,0,0,0] v = c0*v 0 + c1*v 2 + c2*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 8)) = c0*v 0 + c1*v 2 + c2*v 8
    ac_rfl

theorem dot_13_329 (c0 c1 c2 c3 : ℂ) (v : Fin 13→ℂ) :
    dotProduct ![c0,0,0,c1,0,0,c2,0,c3,0,0,0,0] v = c0*v 0 + c1*v 3 + c2*v 6 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 6 + (c3*v 8))) = c0*v 0 + c1*v 3 + c2*v 6 + c3*v 8
    ac_rfl

theorem dot_13_35 (c0 c1 c2 : ℂ) (v : Fin 13→ℂ) :
    dotProduct ![c0,c1,0,0,0,c2,0,0,0,0,0,0,0] v = c0*v 0 + c1*v 1 + c2*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 5)) = c0*v 0 + c1*v 1 + c2*v 5
    ac_rfl

theorem dot_13_4224 (c0 c1 : ℂ) (v : Fin 13→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,c1] v = c0*v 7 + c1*v 12 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 12) = c0*v 7 + c1*v 12
    ac_rfl

theorem dot_13_579 (c0 c1 c2 c3 : ℂ) (v : Fin 13→ℂ) :
    dotProduct ![c0,c1,0,0,0,0,c2,0,0,c3,0,0,0] v = c0*v 0 + c1*v 1 + c2*v 6 + c3*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 6 + (c3*v 9))) = c0*v 0 + c1*v 1 + c2*v 6 + c3*v 9
    ac_rfl

theorem dot_13_585 (c0 c1 c2 c3 : ℂ) (v : Fin 13→ℂ) :
    dotProduct ![c0,0,0,c1,0,0,c2,0,0,c3,0,0,0] v = c0*v 0 + c1*v 3 + c2*v 6 + c3*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 6 + (c3*v 9))) = c0*v 0 + c1*v 3 + c2*v 6 + c3*v 9
    ac_rfl

theorem dot_13_6196 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 13→ℂ) :
    dotProduct ![0,0,c0,0,c1,c2,0,0,0,0,0,c3,c4] v = c0*v 2 + c1*v 4 + c2*v 5 + c3*v 11 + c4*v 12 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 5 + (c3*v 11 + (c4*v 12)))) = c0*v 2 + c1*v 4 + c2*v 5 + c3*v 11 + c4*v 12
    ac_rfl

theorem dot_13_73 (c0 c1 c2 : ℂ) (v : Fin 13→ℂ) :
    dotProduct ![c0,0,0,c1,0,0,c2,0,0,0,0,0,0] v = c0*v 0 + c1*v 3 + c2*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 6)) = c0*v 0 + c1*v 3 + c2*v 6
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_14_132 (c0 c1 : ℂ) (v : Fin 14→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,c1,0,0,0,0,0,0] v = c0*v 2 + c1*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 7) = c0*v 2 + c1*v 7
    ac_rfl

theorem dot_14_1425 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 14→ℂ) :
    dotProduct ![c0,0,0,0,c1,0,0,c2,c3,0,c4,0,0,0] v = c0*v 0 + c1*v 4 + c2*v 7 + c3*v 8 + c4*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 4 + (c2*v 7 + (c3*v 8 + (c4*v 10)))) = c0*v 0 + c1*v 4 + c2*v 7 + c3*v 8 + c4*v 10
    ac_rfl

theorem dot_14_1568 (c0 c1 c2 : ℂ) (v : Fin 14→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,c1,c2,0,0,0] v = c0*v 5 + c1*v 9 + c2*v 10 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 9 + (c2*v 10)) = c0*v 5 + c1*v 9 + c2*v 10
    ac_rfl

theorem dot_14_2050 (c0 c1 : ℂ) (v : Fin 14→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,0,0,0,c1,0,0] v = c0*v 1 + c1*v 11 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 11) = c0*v 1 + c1*v 11
    ac_rfl

theorem dot_14_2060 (c0 c1 c2 : ℂ) (v : Fin 14→ℂ) :
    dotProduct ![0,0,c0,c1,0,0,0,0,0,0,0,c2,0,0] v = c0*v 2 + c1*v 3 + c2*v 11 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 3 + (c2*v 11)) = c0*v 2 + c1*v 3 + c2*v 11
    ac_rfl

theorem dot_14_258 (c0 c1 : ℂ) (v : Fin 14→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,c1,0,0,0,0,0] v = c0*v 1 + c1*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 8) = c0*v 1 + c1*v 8
    ac_rfl

theorem dot_14_2632 (c0 c1 c2 c3 : ℂ) (v : Fin 14→ℂ) :
    dotProduct ![0,0,0,c0,0,0,c1,0,0,c2,0,c3,0,0] v = c0*v 3 + c1*v 6 + c2*v 9 + c3*v 11 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 6 + (c2*v 9 + (c3*v 11))) = c0*v 3 + c1*v 6 + c2*v 9 + c3*v 11
    ac_rfl

theorem dot_14_4136 (c0 c1 c2 : ℂ) (v : Fin 14→ℂ) :
    dotProduct ![0,0,0,c0,0,c1,0,0,0,0,0,0,c2,0] v = c0*v 3 + c1*v 5 + c2*v 12 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 5 + (c2*v 12)) = c0*v 3 + c1*v 5 + c2*v 12
    ac_rfl

theorem dot_14_4680 (c0 c1 c2 c3 : ℂ) (v : Fin 14→ℂ) :
    dotProduct ![0,0,0,c0,0,0,c1,0,0,c2,0,0,c3,0] v = c0*v 3 + c1*v 6 + c2*v 9 + c3*v 12 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 6 + (c2*v 9 + (c3*v 12))) = c0*v 3 + c1*v 6 + c2*v 9 + c3*v 12
    ac_rfl

theorem dot_14_4688 (c0 c1 c2 c3 : ℂ) (v : Fin 14→ℂ) :
    dotProduct ![0,0,0,0,c0,0,c1,0,0,c2,0,0,c3,0] v = c0*v 4 + c1*v 6 + c2*v 9 + c3*v 12 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 + (c1*v 6 + (c2*v 9 + (c3*v 12))) = c0*v 4 + c1*v 6 + c2*v 9 + c3*v 12
    ac_rfl

theorem dot_14_584 (c0 c1 c2 : ℂ) (v : Fin 14→ℂ) :
    dotProduct ![0,0,0,c0,0,0,c1,0,0,c2,0,0,0,0] v = c0*v 3 + c1*v 6 + c2*v 9 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 6 + (c2*v 9)) = c0*v 3 + c1*v 6 + c2*v 9
    ac_rfl

theorem dot_14_8193 (c0 c1 : ℂ) (v : Fin 14→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0,0,0,0,0,c1] v = c0*v 0 + c1*v 13 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 13) = c0*v 0 + c1*v 13
    ac_rfl

theorem dot_14_8704 (c0 c1 : ℂ) (v : Fin 14→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,c0,0,0,0,c1] v = c0*v 9 + c1*v 13 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 9 + (c1*v 13) = c0*v 9 + c1*v 13
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_39_100663424 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,c2,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 7 + c1*v 25 + c2*v 26 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 25 + (c2*v 26)) = c0*v 7 + c1*v 25 + c2*v 26
    ac_rfl

theorem dot_39_1048576 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 20 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 20 = c0*v 20
    ac_rfl

theorem dot_39_1073742016 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 7 + c2*v 30 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 7 + (c2*v 30)) = c0*v 6 + c1*v 7 + c2*v 30
    ac_rfl

theorem dot_39_1073743872 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0] v = c0*v 11 + c1*v 30 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 11 + (c1*v 30) = c0*v 11 + c1*v 30
    ac_rfl

theorem dot_39_131136 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17) = c0*v 6 + c1*v 17
    ac_rfl

theorem dot_39_131200 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 7 + c1*v 17 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 17) = c0*v 7 + c1*v 17
    ac_rfl

theorem dot_39_134225920 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 13 + c1*v 27 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 13 + (c1*v 27) = c0*v 13 + c1*v 27
    ac_rfl

theorem dot_39_137438953472 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0] v = c0*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 37 = c0*v 37
    ac_rfl

theorem dot_39_137438953984 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0] v = c0*v 9 + c1*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 9 + (c1*v 37) = c0*v 9 + c1*v 37
    ac_rfl

theorem dot_39_16448 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 14 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 14) = c0*v 6 + c1*v 14
    ac_rfl

theorem dot_39_16 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 = c0*v 4
    ac_rfl

theorem dot_39_17188257792 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0] v = c0*v 23 + c1*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 23 + (c1*v 34) = c0*v 23 + c1*v 34
    ac_rfl

theorem dot_39_17196646400 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0] v = c0*v 24 + c1*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 24 + (c1*v 34) = c0*v 24 + c1*v 34
    ac_rfl

theorem dot_39_19327352960 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,c2,0,0,0,0] v = c0*v 7 + c1*v 31 + c2*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 31 + (c2*v 34)) = c0*v 7 + c1*v 31 + c2*v 34
    ac_rfl

theorem dot_39_1 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 0 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 = c0*v 0
    ac_rfl

theorem dot_39_2097152 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 21 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 21 = c0*v 21
    ac_rfl

theorem dot_39_2147483652 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0] v = c0*v 2 + c1*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 31) = c0*v 2 + c1*v 31
    ac_rfl

theorem dot_39_2147483744 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 6 + c2*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 6 + (c2*v 31)) = c0*v 5 + c1*v 6 + c2*v 31
    ac_rfl

theorem dot_39_2147483840 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 7 + c2*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 7 + (c2*v 31)) = c0*v 6 + c1*v 7 + c2*v 31
    ac_rfl

theorem dot_39_2147487872 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0] v = c0*v 7 + c1*v 12 + c2*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 12 + (c2*v 31)) = c0*v 7 + c1*v 12 + c2*v 31
    ac_rfl

theorem dot_39_2181070912 (c0 c1 c2 c3 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,c3,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 15 + c2*v 25 + c3*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 15 + (c2*v 25 + (c3*v 31))) = c0*v 6 + c1*v 15 + c2*v 25 + c3*v 31
    ac_rfl

theorem dot_39_2181136384 (c0 c1 c2 c3 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,c3,0,0,0,0,0,0,0] v = c0*v 15 + c1*v 16 + c2*v 25 + c3*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 15 + (c1*v 16 + (c2*v 25 + (c3*v 31))) = c0*v 15 + c1*v 16 + c2*v 25 + c3*v 31
    ac_rfl

theorem dot_39_2415919232 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,c2,0,0,0,0,0,0,0] v = c0*v 7 + c1*v 28 + c2*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 28 + (c2*v 31)) = c0*v 7 + c1*v 28 + c2*v 31
    ac_rfl

theorem dot_39_262656 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 9 + c1*v 18 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 9 + (c1*v 18) = c0*v 9 + c1*v 18
    ac_rfl

theorem dot_39_264192 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 11 + c1*v 18 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 11 + (c1*v 18) = c0*v 11 + c1*v 18
    ac_rfl

theorem dot_39_274877906944 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0] v = c0*v 38 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 38 = c0*v 38
    ac_rfl

theorem dot_39_2 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 1 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 = c0*v 1
    ac_rfl

theorem dot_39_302022720 (c0 c1 c2 c3 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,c2,0,0,c3,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 15 + c2*v 25 + c3*v 28 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 15 + (c2*v 25 + (c3*v 28))) = c0*v 6 + c1*v 15 + c2*v 25 + c3*v 28
    ac_rfl

theorem dot_39_32800 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 15 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 15) = c0*v 5 + c1*v 15
    ac_rfl

theorem dot_39_33554440 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 3 + c1*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 25) = c0*v 3 + c1*v 25
    ac_rfl

theorem dot_39_33558592 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 12 + c2*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 12 + (c2*v 25)) = c0*v 6 + c1*v 12 + c2*v 25
    ac_rfl

theorem dot_39_33587520 (c0 c1 c2 c3 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,c1,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 8 + c2*v 15 + c3*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 8 + (c2*v 15 + (c3*v 25))) = c0*v 6 + c1*v 8 + c2*v 15 + c3*v 25
    ac_rfl

theorem dot_39_33589248 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 11 + c1*v 15 + c2*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 11 + (c1*v 15 + (c2*v 25)) = c0*v 11 + c1*v 15 + c2*v 25
    ac_rfl

theorem dot_39_34393292800 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0] v = c0*v 25 + c1*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 25 + (c1*v 35) = c0*v 25 + c1*v 35
    ac_rfl

theorem dot_39_34493956096 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0] v = c0*v 27 + c1*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 27 + (c1*v 35) = c0*v 27 + c1*v 35
    ac_rfl

theorem dot_39_4194308 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 2 + c1*v 22 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 22) = c0*v 2 + c1*v 22
    ac_rfl

theorem dot_39_4299161600 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0] v = c0*v 22 + c1*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 22 + (c1*v 32) = c0*v 22 + c1*v 32
    ac_rfl

theorem dot_39_4328522816 (c0 c1 c2 c3 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,c3,0,0,0,0,0,0] v = c0*v 6 + c1*v 10 + c2*v 25 + c3*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 10 + (c2*v 25 + (c3*v 32))) = c0*v 6 + c1*v 10 + c2*v 25 + c3*v 32
    ac_rfl

theorem dot_39_4328554560 (c0 c1 c2 c3 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,c3,0,0,0,0,0,0] v = c0*v 6 + c1*v 15 + c2*v 25 + c3*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 15 + (c2*v 25 + (c3*v 32))) = c0*v 6 + c1*v 15 + c2*v 25 + c3*v 32
    ac_rfl

theorem dot_39_4328554624 (c0 c1 c2 c3 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,c3,0,0,0,0,0,0] v = c0*v 7 + c1*v 15 + c2*v 25 + c3*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 15 + (c2*v 25 + (c3*v 32))) = c0*v 7 + c1*v 15 + c2*v 25 + c3*v 32
    ac_rfl

theorem dot_39_4328554752 (c0 c1 c2 c3 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,c3,0,0,0,0,0,0] v = c0*v 8 + c1*v 15 + c2*v 25 + c3*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 + (c1*v 15 + (c2*v 25 + (c3*v 32))) = c0*v 8 + c1*v 15 + c2*v 25 + c3*v 32
    ac_rfl

theorem dot_39_49280 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,c1,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 7 + c1*v 14 + c2*v 15 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 14 + (c2*v 15)) = c0*v 7 + c1*v 14 + c2*v 15
    ac_rfl

theorem dot_39_4 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 2 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 = c0*v 2
    ac_rfl

theorem dot_39_50364480 (c0 c1 c2 c3 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,c2,c3,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 15 + c2*v 24 + c3*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 15 + (c2*v 24 + (c3*v 25))) = c0*v 6 + c1*v 15 + c2*v 24 + c3*v 25
    ac_rfl

theorem dot_39_524288 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 19 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 19 = c0*v 19
    ac_rfl

theorem dot_39_532575944635 (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![c0,c1,0,c2,c3,c4,0,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,0,c32,c33,c34,c35] v = c0*v 0 + c1*v 1 + c2*v 3 + c3*v 4 + c4*v 5 + c5*v 7 + c6*v 8 + c7*v 9 + c8*v 10 + c9*v 11 + c10*v 12 + c11*v 13 + c12*v 14 + c13*v 15 + c14*v 16 + c15*v 17 + c16*v 18 + c17*v 19 + c18*v 20 + c19*v 21 + c20*v 22 + c21*v 23 + c22*v 24 + c23*v 25 + c24*v 26 + c25*v 27 + c26*v 28 + c27*v 29 + c28*v 30 + c29*v 31 + c30*v 32 + c31*v 33 + c32*v 35 + c33*v 36 + c34*v 37 + c35*v 38 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 3 + (c3*v 4 + (c4*v 5 + (c5*v 7 + (c6*v 8 + (c7*v 9 + (c8*v 10 + (c9*v 11 + (c10*v 12 + (c11*v 13 + (c12*v 14 + (c13*v 15 + (c14*v 16 + (c15*v 17 + (c16*v 18 + (c17*v 19 + (c18*v 20 + (c19*v 21 + (c20*v 22 + (c21*v 23 + (c22*v 24 + (c23*v 25 + (c24*v 26 + (c25*v 27 + (c26*v 28 + (c27*v 29 + (c28*v 30 + (c29*v 31 + (c30*v 32 + (c31*v 33 + (c32*v 35 + (c33*v 36 + (c34*v 37 + (c35*v 38))))))))))))))))))))))))))))))))))) = c0*v 0 + c1*v 1 + c2*v 3 + c3*v 4 + c4*v 5 + c5*v 7 + c6*v 8 + c7*v 9 + c8*v 10 + c9*v 11 + c10*v 12 + c11*v 13 + c12*v 14 + c13*v 15 + c14*v 16 + c15*v 17 + c16*v 18 + c17*v 19 + c18*v 20 + c19*v 21 + c20*v 22 + c21*v 23 + c22*v 24 + c23*v 25 + c24*v 26 + c25*v 27 + c26*v 28 + c27*v 29 + c28*v 30 + c29*v 31 + c30*v 32 + c31*v 33 + c32*v 35 + c33*v 36 + c34*v 37 + c35*v 38
    ac_rfl

theorem dot_39_536871936 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0] v = c0*v 10 + c1*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 10 + (c1*v 29) = c0*v 10 + c1*v 29
    ac_rfl

theorem dot_39_545460846399 (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![c0,c1,c2,c3,c4,c5,0,0,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,0,c30,c31,c32,c33,c34,c35] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 8 + c7*v 9 + c8*v 10 + c9*v 11 + c10*v 12 + c11*v 13 + c12*v 14 + c13*v 15 + c14*v 16 + c15*v 17 + c16*v 18 + c17*v 19 + c18*v 20 + c19*v 21 + c20*v 22 + c21*v 23 + c22*v 24 + c23*v 25 + c24*v 26 + c25*v 27 + c26*v 28 + c27*v 29 + c28*v 30 + c29*v 31 + c30*v 33 + c31*v 34 + c32*v 35 + c33*v 36 + c34*v 37 + c35*v 38 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 3 + (c4*v 4 + (c5*v 5 + (c6*v 8 + (c7*v 9 + (c8*v 10 + (c9*v 11 + (c10*v 12 + (c11*v 13 + (c12*v 14 + (c13*v 15 + (c14*v 16 + (c15*v 17 + (c16*v 18 + (c17*v 19 + (c18*v 20 + (c19*v 21 + (c20*v 22 + (c21*v 23 + (c22*v 24 + (c23*v 25 + (c24*v 26 + (c25*v 27 + (c26*v 28 + (c27*v 29 + (c28*v 30 + (c29*v 31 + (c30*v 33 + (c31*v 34 + (c32*v 35 + (c33*v 36 + (c34*v 37 + (c35*v 38))))))))))))))))))))))))))))))))))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 8 + c7*v 9 + c8*v 10 + c9*v 11 + c10*v 12 + c11*v 13 + c12*v 14 + c13*v 15 + c14*v 16 + c15*v 17 + c16*v 18 + c17*v 19 + c18*v 20 + c19*v 21 + c20*v 22 + c21*v 23 + c22*v 24 + c23*v 25 + c24*v 26 + c25*v 27 + c26*v 28 + c27*v 29 + c28*v 30 + c29*v 31 + c30*v 33 + c31*v 34 + c32*v 35 + c33*v 36 + c34*v 37 + c35*v 38
    ac_rfl

theorem dot_39_570458112 (c0 c1 c2 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,c2,0,0,0,0,0,0,0,0,0] v = c0*v 15 + c1*v 25 + c2*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 15 + (c1*v 25 + (c2*v 29)) = c0*v 15 + c1*v 25 + c2*v 29
    ac_rfl

theorem dot_39_65600 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 16 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 16) = c0*v 6 + c1*v 16
    ac_rfl

theorem dot_39_67108928 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 26 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 26) = c0*v 6 + c1*v 26
    ac_rfl

theorem dot_39_68719476736 (c0 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0] v = c0*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 36 = c0*v 36
    ac_rfl

theorem dot_39_68719476864 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0] v = c0*v 7 + c1*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 36) = c0*v 7 + c1*v 36
    ac_rfl

theorem dot_39_8256 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 13 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 13) = c0*v 6 + c1*v 13
    ac_rfl

theorem dot_39_8388616 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 3 + c1*v 23 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 23) = c0*v 3 + c1*v 23
    ac_rfl

theorem dot_39_8388672 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 23 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 23) = c0*v 6 + c1*v 23
    ac_rfl

theorem dot_39_8388736 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 7 + c1*v 23 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 23) = c0*v 7 + c1*v 23
    ac_rfl

theorem dot_39_8589934656 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0] v = c0*v 6 + c1*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 33) = c0*v 6 + c1*v 33
    ac_rfl

theorem dot_39_8598323200 (c0 c1 : ℂ) (v : Fin 39→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0] v = c0*v 23 + c1*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 23 + (c1*v 33) = c0*v 23 + c1*v 33
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_40_1048576 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 20 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 20 = c0*v 20
    ac_rfl

theorem dot_40_1075838976 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0] v = c0*v 21 + c1*v 30 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 21 + (c1*v 30) = c0*v 21 + c1*v 30
    ac_rfl

theorem dot_40_1081778110335 (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![c0,c1,c2,c3,c4,c5,c6,0,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,0,c23,c24,c25,c26,0,c27,c28,c29,c30,0,c31,c32,c33,c34,c35] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 8 + c8*v 9 + c9*v 10 + c10*v 11 + c11*v 12 + c12*v 13 + c13*v 14 + c14*v 15 + c15*v 16 + c16*v 17 + c17*v 18 + c18*v 19 + c19*v 20 + c20*v 21 + c21*v 22 + c22*v 23 + c23*v 25 + c24*v 26 + c25*v 27 + c26*v 28 + c27*v 30 + c28*v 31 + c29*v 32 + c30*v 33 + c31*v 35 + c32*v 36 + c33*v 37 + c34*v 38 + c35*v 39 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 3 + (c4*v 4 + (c5*v 5 + (c6*v 6 + (c7*v 8 + (c8*v 9 + (c9*v 10 + (c10*v 11 + (c11*v 12 + (c12*v 13 + (c13*v 14 + (c14*v 15 + (c15*v 16 + (c16*v 17 + (c17*v 18 + (c18*v 19 + (c19*v 20 + (c20*v 21 + (c21*v 22 + (c22*v 23 + (c23*v 25 + (c24*v 26 + (c25*v 27 + (c26*v 28 + (c27*v 30 + (c28*v 31 + (c29*v 32 + (c30*v 33 + (c31*v 35 + (c32*v 36 + (c33*v 37 + (c34*v 38 + (c35*v 39))))))))))))))))))))))))))))))))))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 8 + c8*v 9 + c9*v 10 + c10*v 11 + c11*v 12 + c12*v 13 + c13*v 14 + c14*v 15 + c15*v 16 + c16*v 17 + c17*v 18 + c18*v 19 + c19*v 20 + c20*v 21 + c21*v 22 + c22*v 23 + c23*v 25 + c24*v 26 + c25*v 27 + c26*v 28 + c27*v 30 + c28*v 31 + c29*v 32 + c30*v 33 + c31*v 35 + c32*v 36 + c33*v 37 + c34*v 38 + c35*v 39
    ac_rfl

theorem dot_40_131200 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 7 + c1*v 17 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 17) = c0*v 7 + c1*v 17
    ac_rfl

theorem dot_40_134221824 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 27 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 27) = c0*v 12 + c1*v 27
    ac_rfl

theorem dot_40_137438969856 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0] v = c0*v 14 + c1*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 14 + (c1*v 37) = c0*v 14 + c1*v 37
    ac_rfl

theorem dot_40_16779296 (c0 c1 c2 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 11 + c2*v 24 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 11 + (c2*v 24)) = c0*v 5 + c1*v 11 + c2*v 24
    ac_rfl

theorem dot_40_17179869728 (c0 c1 c2 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0] v = c0*v 5 + c1*v 9 + c2*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 9 + (c2*v 34)) = c0*v 5 + c1*v 9 + c2*v 34
    ac_rfl

theorem dot_40_17213440032 (c0 c1 c2 c3 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,c3,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 25 + (c3*v 34))) = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 34
    ac_rfl

theorem dot_40_17213440128 (c0 c1 c2 c3 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,c3,0,0,0,0,0] v = c0*v 7 + c1*v 14 + c2*v 25 + c3*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 14 + (c2*v 25 + (c3*v 34))) = c0*v 7 + c1*v 14 + c2*v 25 + c3*v 34
    ac_rfl

theorem dot_40_1 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 0 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 = c0*v 0
    ac_rfl

theorem dot_40_2181054496 (c0 c1 c2 c3 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,c3,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 25 + (c3*v 31))) = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 31
    ac_rfl

theorem dot_40_262144 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 18 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 18 = c0*v 18
    ac_rfl

theorem dot_40_268451872 (c0 c1 c2 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 28 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 28)) = c0*v 5 + c1*v 14 + c2*v 28
    ac_rfl

theorem dot_40_274877906944 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0] v = c0*v 38 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 38 = c0*v 38
    ac_rfl

theorem dot_40_2 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 1 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 = c0*v 1
    ac_rfl

theorem dot_40_33571840 (c0 c1 c2 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 10 + c1*v 14 + c2*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 10 + (c1*v 14 + (c2*v 25)) = c0*v 10 + c1*v 14 + c2*v 25
    ac_rfl

theorem dot_40_38654705696 (c0 c1 c2 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,c2,0,0,0,0] v = c0*v 5 + c1*v 32 + c2*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 32 + (c2*v 35)) = c0*v 5 + c1*v 32 + c2*v 35
    ac_rfl

theorem dot_40_4112 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 4 + c1*v 12 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 + (c1*v 12) = c0*v 4 + c1*v 12
    ac_rfl

theorem dot_40_4128 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 12 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 12) = c0*v 5 + c1*v 12
    ac_rfl

theorem dot_40_4194336 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 22 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 22) = c0*v 5 + c1*v 22
    ac_rfl

theorem dot_40_41959456 (c0 c1 c2 c3 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,c2,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 23 + c3*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 23 + (c3*v 25))) = c0*v 5 + c1*v 14 + c2*v 23 + c3*v 25
    ac_rfl

theorem dot_40_4202496 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 13 + c1*v 22 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 13 + (c1*v 22) = c0*v 13 + c1*v 22
    ac_rfl

theorem dot_40_4294967300 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0] v = c0*v 2 + c1*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 32) = c0*v 2 + c1*v 32
    ac_rfl

theorem dot_40_4294967552 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0] v = c0*v 8 + c1*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 + (c1*v 32) = c0*v 8 + c1*v 32
    ac_rfl

theorem dot_40_4328538144 (c0 c1 c2 c3 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,c3,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 25 + (c3*v 32))) = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 32
    ac_rfl

theorem dot_40_50348064 (c0 c1 c2 c3 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,c2,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 24 + c3*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 24 + (c3*v 25))) = c0*v 5 + c1*v 14 + c2*v 24 + c3*v 25
    ac_rfl

theorem dot_40_524288 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 19 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 19 = c0*v 19
    ac_rfl

theorem dot_40_536903712 (c0 c1 c2 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 15 + c2*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 15 + (c2*v 29)) = c0*v 5 + c1*v 15 + c2*v 29
    ac_rfl

theorem dot_40_549755813888 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0] v = c0*v 39 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 39 = c0*v 39
    ac_rfl

theorem dot_40_570441760 (c0 c1 c2 c3 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,c3,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 25 + (c3*v 29))) = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 29
    ac_rfl

theorem dot_40_65568 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 16 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 16) = c0*v 5 + c1*v 16
    ac_rfl

theorem dot_40_67108896 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 26 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 26) = c0*v 5 + c1*v 26
    ac_rfl

theorem dot_40_68719476736 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0] v = c0*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 36 = c0*v 36
    ac_rfl

theorem dot_40_8623505440 (c0 c1 c2 c3 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,c3,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 25 + (c3*v 33))) = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 33
    ac_rfl

theorem dot_40_8 (c0 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 3 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 = c0*v 3
    ac_rfl

theorem dot_40_96 (c0 c1 : ℂ) (v : Fin 40→ℂ) :
    dotProduct ![0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 6) = c0*v 5 + c1*v 6
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_43_100679712 (c0 c1 c2 c3 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 26 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 25 + (c3*v 26))) = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 26
    ac_rfl

theorem dot_43_1099511627904 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0] v = c0*v 7 + c1*v 40 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 40) = c0*v 7 + c1*v 40
    ac_rfl

theorem dot_43_1107312640 (c0 c1 c2 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 14 + c1*v 25 + c2*v 30 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 14 + (c1*v 25 + (c2*v 30)) = c0*v 14 + c1*v 25 + c2*v 30
    ac_rfl

theorem dot_43_12582912 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 22 + c1*v 23 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 22 + (c1*v 23) = c0*v 22 + c1*v 23
    ac_rfl

theorem dot_43_131104 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 17 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 17) = c0*v 5 + c1*v 17
    ac_rfl

theorem dot_43_134225952 (c0 c1 c2 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 13 + c2*v 27 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 13 + (c2*v 27)) = c0*v 5 + c1*v 13 + c2*v 27
    ac_rfl

theorem dot_43_137439035424 (c0 c1 c2 c3 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 16 + c3*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 16 + (c3*v 37))) = c0*v 5 + c1*v 14 + c2*v 16 + c3*v 37
    ac_rfl

theorem dot_43_167772192 (c0 c1 c2 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 25 + c2*v 27 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 25 + (c2*v 27)) = c0*v 5 + c1*v 25 + c2*v 27
    ac_rfl

theorem dot_43_17213440032 (c0 c1 c2 c3 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 25 + (c3*v 34))) = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 34
    ac_rfl

theorem dot_43_1 (c0 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 0 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 = c0*v 0
    ac_rfl

theorem dot_43_2097152 (c0 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 21 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 21 = c0*v 21
    ac_rfl

theorem dot_43_2147484160 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 9 + c1*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 9 + (c1*v 31) = c0*v 9 + c1*v 31
    ac_rfl

theorem dot_43_2199023255552 (c0 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0] v = c0*v 41 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 41 = c0*v 41
    ac_rfl

theorem dot_43_268435520 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 28 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 28) = c0*v 6 + c1*v 28
    ac_rfl

theorem dot_43_268439552 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 28 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 28) = c0*v 12 + c1*v 28
    ac_rfl

theorem dot_43_274877906948 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0] v = c0*v 2 + c1*v 38 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 38) = c0*v 2 + c1*v 38
    ac_rfl

theorem dot_43_274911461376 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0] v = c0*v 25 + c1*v 38 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 25 + (c1*v 38) = c0*v 25 + c1*v 38
    ac_rfl

theorem dot_43_2 (c0 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 1 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 = c0*v 1
    ac_rfl

theorem dot_43_33571104 (c0 c1 c2 c3 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,c1,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 8 + c2*v 14 + c3*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 8 + (c2*v 14 + (c3*v 25))) = c0*v 5 + c1*v 8 + c2*v 14 + c3*v 25
    ac_rfl

theorem dot_43_33571840 (c0 c1 c2 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 10 + c1*v 14 + c2*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 10 + (c1*v 14 + (c2*v 25)) = c0*v 10 + c1*v 14 + c2*v 25
    ac_rfl

theorem dot_43_33572896 (c0 c1 c2 c3 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,c1,0,0,c2,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 11 + c2*v 14 + c3*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 11 + (c2*v 14 + (c3*v 25))) = c0*v 5 + c1*v 11 + c2*v 14 + c3*v 25
    ac_rfl

theorem dot_43_33832992 (c0 c1 c2 c3 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,c2,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 18 + c3*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 18 + (c3*v 25))) = c0*v 5 + c1*v 14 + c2*v 18 + c3*v 25
    ac_rfl

theorem dot_43_34393293344 (c0 c1 c2 c3 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 9 + c2*v 25 + c3*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 9 + (c2*v 25 + (c3*v 35))) = c0*v 5 + c1*v 9 + c2*v 25 + c3*v 35
    ac_rfl

theorem dot_43_34393309216 (c0 c1 c2 c3 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 25 + (c3*v 35))) = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 35
    ac_rfl

theorem dot_43_4128 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 12 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 12) = c0*v 5 + c1*v 12
    ac_rfl

theorem dot_43_4295000096 (c0 c1 c2 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 15 + c2*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 15 + (c2*v 32)) = c0*v 5 + c1*v 15 + c2*v 32
    ac_rfl

theorem dot_43_4328538144 (c0 c1 c2 c3 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 25 + (c3*v 32))) = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 32
    ac_rfl

theorem dot_43_4399120252928 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,c1] v = c0*v 30 + c1*v 42 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 30 + (c1*v 42) = c0*v 30 + c1*v 42
    ac_rfl

theorem dot_43_48 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 4 + c1*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 + (c1*v 5) = c0*v 4 + c1*v 5
    ac_rfl

theorem dot_43_50331680 (c0 c1 c2 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 24 + c2*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 24 + (c2*v 25)) = c0*v 5 + c1*v 24 + c2*v 25
    ac_rfl

theorem dot_43_524288 (c0 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 19 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 19 = c0*v 19
    ac_rfl

theorem dot_43_549755813888 (c0 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0] v = c0*v 39 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 39 = c0*v 39
    ac_rfl

theorem dot_43_570441760 (c0 c1 c2 c3 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 25 + (c3*v 29))) = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 29
    ac_rfl

theorem dot_43_68727865344 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0] v = c0*v 23 + c1*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 23 + (c1*v 36) = c0*v 23 + c1*v 36
    ac_rfl

theorem dot_43_8388640 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 23 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 23) = c0*v 5 + c1*v 23
    ac_rfl

theorem dot_43_8482157690367 (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![c0,c1,c2,c3,c4,c5,c6,c7,c8,0,c9,c10,c11,c12,c13,c14,0,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,0,0,c25,c26,c27,0,c28,c29,0,c30,c31,0,c32,c33,c34,c35] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 7 + c8*v 8 + c9*v 10 + c10*v 11 + c11*v 12 + c12*v 13 + c13*v 14 + c14*v 15 + c15*v 17 + c16*v 18 + c17*v 19 + c18*v 20 + c19*v 21 + c20*v 22 + c21*v 23 + c22*v 24 + c23*v 25 + c24*v 26 + c25*v 29 + c26*v 30 + c27*v 31 + c28*v 33 + c29*v 34 + c30*v 36 + c31*v 37 + c32*v 39 + c33*v 40 + c34*v 41 + c35*v 42 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 3 + (c4*v 4 + (c5*v 5 + (c6*v 6 + (c7*v 7 + (c8*v 8 + (c9*v 10 + (c10*v 11 + (c11*v 12 + (c12*v 13 + (c13*v 14 + (c14*v 15 + (c15*v 17 + (c16*v 18 + (c17*v 19 + (c18*v 20 + (c19*v 21 + (c20*v 22 + (c21*v 23 + (c22*v 24 + (c23*v 25 + (c24*v 26 + (c25*v 29 + (c26*v 30 + (c27*v 31 + (c28*v 33 + (c29*v 34 + (c30*v 36 + (c31*v 37 + (c32*v 39 + (c33*v 40 + (c34*v 41 + (c35*v 42))))))))))))))))))))))))))))))))))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 7 + c8*v 8 + c9*v 10 + c10*v 11 + c11*v 12 + c12*v 13 + c13*v 14 + c14*v 15 + c15*v 17 + c16*v 18 + c17*v 19 + c18*v 20 + c19*v 21 + c20*v 22 + c21*v 23 + c22*v 24 + c23*v 25 + c24*v 26 + c25*v 29 + c26*v 30 + c27*v 31 + c28*v 33 + c29*v 34 + c30*v 36 + c31*v 37 + c32*v 39 + c33*v 40 + c34*v 41 + c35*v 42
    ac_rfl

theorem dot_43_8589934720 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0] v = c0*v 7 + c1*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 7 + (c1*v 33) = c0*v 7 + c1*v 33
    ac_rfl

theorem dot_43_8590983168 (c0 c1 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0] v = c0*v 20 + c1*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 20 + (c1*v 33) = c0*v 20 + c1*v 33
    ac_rfl

theorem dot_43_8623505440 (c0 c1 c2 c3 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 14 + (c2*v 25 + (c3*v 33))) = c0*v 5 + c1*v 14 + c2*v 25 + c3*v 33
    ac_rfl

theorem dot_43_8623570944 (c0 c1 c2 c3 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,c1,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0] v = c0*v 14 + c1*v 16 + c2*v 25 + c3*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 14 + (c1*v 16 + (c2*v 25 + (c3*v 33))) = c0*v 14 + c1*v 16 + c2*v 25 + c3*v 33
    ac_rfl

theorem dot_43_8 (c0 : ℂ) (v : Fin 43→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 3 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 = c0*v 3
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_45_1048640 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 20 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 20) = c0*v 6 + c1*v 20
    ac_rfl

theorem dot_45_1073774656 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 15 + c2*v 30 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 15 + (c2*v 30)) = c0*v 6 + c1*v 15 + c2*v 30
    ac_rfl

theorem dot_45_1099545182208 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0] v = c0*v 25 + c1*v 40 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 25 + (c1*v 40) = c0*v 25 + c1*v 40
    ac_rfl

theorem dot_45_13194139533312 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,c1,0] v = c0*v 42 + c1*v 43 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 42 + (c1*v 43) = c0*v 42 + c1*v 43
    ac_rfl

theorem dot_45_137438954048 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 9 + c2*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 9 + (c2*v 37)) = c0*v 6 + c1*v 9 + c2*v 37
    ac_rfl

theorem dot_45_137975825472 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 10 + c2*v 29 + c3*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 10 + (c2*v 29 + (c3*v 37))) = c0*v 6 + c1*v 10 + c2*v 29 + c3*v 37
    ac_rfl

theorem dot_45_137975955520 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 + c2*v 29 + c3*v 37 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17 + (c2*v 29 + (c3*v 37))) = c0*v 6 + c1*v 17 + c2*v 29 + c3*v 37
    ac_rfl

theorem dot_45_163904 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,c1,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 15 + c2*v 17 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 15 + (c2*v 17)) = c0*v 6 + c1*v 15 + c2*v 17
    ac_rfl

theorem dot_45_16448 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 14 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 14) = c0*v 6 + c1*v 14
    ac_rfl

theorem dot_45_16 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 = c0*v 4
    ac_rfl

theorem dot_45_17179871232 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0] v = c0*v 11 + c1*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 11 + (c1*v 34) = c0*v 11 + c1*v 34
    ac_rfl

theorem dot_45_17592186044416 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0] v = c0*v 44 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 44 = c0*v 44
    ac_rfl

theorem dot_45_17716871232 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 + c2*v 29 + c3*v 34 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17 + (c2*v 29 + (c3*v 34))) = c0*v 6 + c1*v 17 + c2*v 29 + c3*v 34
    ac_rfl

theorem dot_45_1 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 0 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 = c0*v 0
    ac_rfl

theorem dot_45_2097152 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 21 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 21 = c0*v 21
    ac_rfl

theorem dot_45_2147500032 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 14 + c1*v 31 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 14 + (c1*v 31) = c0*v 14 + c1*v 31
    ac_rfl

theorem dot_45_2199023255552 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0] v = c0*v 41 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 41 = c0*v 41
    ac_rfl

theorem dot_45_268436544 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 10 + c2*v 28 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 10 + (c2*v 28)) = c0*v 6 + c1*v 10 + c2*v 28
    ac_rfl

theorem dot_45_274877923328 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0] v = c0*v 14 + c1*v 38 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 14 + (c1*v 38) = c0*v 14 + c1*v 38
    ac_rfl

theorem dot_45_30631505377791 (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![c0,c1,c2,c3,c4,c5,c6,c7,c8,0,0,c9,c10,c11,0,0,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,0,0,c22,c23,c24,c25,c26,c27,0,c28,c29,0,c30,c31,c32,c33,0,c34,c35] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 7 + c8*v 8 + c9*v 11 + c10*v 12 + c11*v 13 + c12*v 16 + c13*v 17 + c14*v 18 + c15*v 19 + c16*v 20 + c17*v 21 + c18*v 22 + c19*v 23 + c20*v 24 + c21*v 25 + c22*v 28 + c23*v 29 + c24*v 30 + c25*v 31 + c26*v 32 + c27*v 33 + c28*v 35 + c29*v 36 + c30*v 38 + c31*v 39 + c32*v 40 + c33*v 41 + c34*v 43 + c35*v 44 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 3 + (c4*v 4 + (c5*v 5 + (c6*v 6 + (c7*v 7 + (c8*v 8 + (c9*v 11 + (c10*v 12 + (c11*v 13 + (c12*v 16 + (c13*v 17 + (c14*v 18 + (c15*v 19 + (c16*v 20 + (c17*v 21 + (c18*v 22 + (c19*v 23 + (c20*v 24 + (c21*v 25 + (c22*v 28 + (c23*v 29 + (c24*v 30 + (c25*v 31 + (c26*v 32 + (c27*v 33 + (c28*v 35 + (c29*v 36 + (c30*v 38 + (c31*v 39 + (c32*v 40 + (c33*v 41 + (c34*v 43 + (c35*v 44))))))))))))))))))))))))))))))))))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 3 + c4*v 4 + c5*v 5 + c6*v 6 + c7*v 7 + c8*v 8 + c9*v 11 + c10*v 12 + c11*v 13 + c12*v 16 + c13*v 17 + c14*v 18 + c15*v 19 + c16*v 20 + c17*v 21 + c18*v 22 + c19*v 23 + c20*v 24 + c21*v 25 + c22*v 28 + c23*v 29 + c24*v 30 + c25*v 31 + c26*v 32 + c27*v 33 + c28*v 35 + c29*v 36 + c30*v 38 + c31*v 39 + c32*v 40 + c33*v 41 + c34*v 43 + c35*v 44
    ac_rfl

theorem dot_45_33554496 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 25 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 25) = c0*v 6 + c1*v 25
    ac_rfl

theorem dot_45_34896740416 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 + c2*v 29 + c3*v 35 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17 + (c2*v 29 + (c3*v 35))) = c0*v 6 + c1*v 17 + c2*v 29 + c3*v 35
    ac_rfl

theorem dot_45_393280 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 + c2*v 18 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17 + (c2*v 18)) = c0*v 6 + c1*v 17 + c2*v 18
    ac_rfl

theorem dot_45_4098 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 1 + c1*v 12 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 12) = c0*v 1 + c1*v 12
    ac_rfl

theorem dot_45_4194560 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 8 + c1*v 22 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 + (c1*v 22) = c0*v 8 + c1*v 22
    ac_rfl

theorem dot_45_4398046642176 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0] v = c0*v 17 + c1*v 42 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 17 + (c1*v 42) = c0*v 17 + c1*v 42
    ac_rfl

theorem dot_45_4831838720 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 9 + c1*v 29 + c2*v 32 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 9 + (c1*v 29 + (c2*v 32)) = c0*v 9 + c1*v 29 + c2*v 32
    ac_rfl

theorem dot_45_4 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 2 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 = c0*v 2
    ac_rfl

theorem dot_45_524352 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 19 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 19) = c0*v 6 + c1*v 19
    ac_rfl

theorem dot_45_537002176 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 7 + c2*v 17 + c3*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 7 + (c2*v 17 + (c3*v 29))) = c0*v 6 + c1*v 7 + c2*v 17 + c3*v 29
    ac_rfl

theorem dot_45_537006080 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 12 + c1*v 17 + c2*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 12 + (c1*v 17 + (c2*v 29)) = c0*v 12 + c1*v 17 + c2*v 29
    ac_rfl

theorem dot_45_537010240 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,c1,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 13 + c2*v 17 + c3*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 13 + (c2*v 17 + (c3*v 29))) = c0*v 6 + c1*v 13 + c2*v 17 + c3*v 29
    ac_rfl

theorem dot_45_537067584 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,c1,c2,0,0,0,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 16 + c2*v 17 + c3*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 16 + (c2*v 17 + (c3*v 29))) = c0*v 6 + c1*v 16 + c2*v 17 + c3*v 29
    ac_rfl

theorem dot_45_549789368320 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0] v = c0*v 25 + c1*v 39 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 25 + (c1*v 39) = c0*v 25 + c1*v 39
    ac_rfl

theorem dot_45_603979872 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,c0,c1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 5 + c1*v 6 + c2*v 26 + c3*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 6 + (c2*v 26 + (c3*v 29))) = c0*v 5 + c1*v 6 + c2*v 26 + c3*v 29
    ac_rfl

theorem dot_45_604110912 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,c2,0,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 + c2*v 26 + c3*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17 + (c2*v 26 + (c3*v 29))) = c0*v 6 + c1*v 17 + c2*v 26 + c3*v 29
    ac_rfl

theorem dot_45_671219776 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,c2,0,c3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 + c2*v 27 + c3*v 29 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17 + (c2*v 27 + (c3*v 29))) = c0*v 6 + c1*v 17 + c2*v 27 + c3*v 29
    ac_rfl

theorem dot_45_68719476744 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0] v = c0*v 3 + c1*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 36) = c0*v 3 + c1*v 36
    ac_rfl

theorem dot_45_68719476992 (c0 c1 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0] v = c0*v 8 + c1*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 + (c1*v 36) = c0*v 8 + c1*v 36
    ac_rfl

theorem dot_45_68870471744 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,c2,0,0,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 24 + c2*v 27 + c3*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 24 + (c2*v 27 + (c3*v 36))) = c0*v 6 + c1*v 24 + c2*v 27 + c3*v 36
    ac_rfl

theorem dot_45_69256478784 (c0 c1 c2 c3 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,0,0,0,0,0,0,0,0,c2,0,0,0,0,0,0,c3,0,0,0,0,0,0,0,0] v = c0*v 6 + c1*v 17 + c2*v 29 + c3*v 36 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 17 + (c2*v 29 + (c3*v 36))) = c0*v 6 + c1*v 17 + c2*v 29 + c3*v 36
    ac_rfl

theorem dot_45_8388608 (c0 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 23 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 23 = c0*v 23
    ac_rfl

theorem dot_45_9126936576 (c0 c1 c2 : ℂ) (v : Fin 45→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c0,0,0,0,0,0,0,0,0,0,0,0,c1,0,0,0,c2,0,0,0,0,0,0,0,0,0,0,0] v = c0*v 17 + c1*v 29 + c2*v 33 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 17 + (c1*v 29 + (c2*v 33)) = c0*v 17 + c1*v 29 + c2*v 33
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_5_13 (c0 c1 c2 : ℂ) (v : Fin 5→ℂ) :
    dotProduct ![c0,0,c1,c2,0] v = c0*v 0 + c1*v 2 + c2*v 3 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 3)) = c0*v 0 + c1*v 2 + c2*v 3
    ac_rfl

theorem dot_5_20 (c0 c1 : ℂ) (v : Fin 5→ℂ) :
    dotProduct ![0,0,c0,0,c1] v = c0*v 2 + c1*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4) = c0*v 2 + c1*v 4
    ac_rfl

theorem dot_5_27 (c0 c1 c2 c3 : ℂ) (v : Fin 5→ℂ) :
    dotProduct ![c0,c1,0,c2,c3] v = c0*v 0 + c1*v 1 + c2*v 3 + c3*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 3 + (c3*v 4))) = c0*v 0 + c1*v 1 + c2*v 3 + c3*v 4
    ac_rfl

theorem dot_5_2 (c0 : ℂ) (v : Fin 5→ℂ) :
    dotProduct ![0,c0,0,0,0] v = c0*v 1 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 = c0*v 1
    ac_rfl

theorem dot_5_5 (c0 c1 : ℂ) (v : Fin 5→ℂ) :
    dotProduct ![c0,0,c1,0,0] v = c0*v 0 + c1*v 2 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2) = c0*v 0 + c1*v 2
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_6_24 (c0 c1 : ℂ) (v : Fin 6→ℂ) :
    dotProduct ![0,0,0,c0,c1,0] v = c0*v 3 + c1*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 4) = c0*v 3 + c1*v 4
    ac_rfl

theorem dot_6_26 (c0 c1 c2 : ℂ) (v : Fin 6→ℂ) :
    dotProduct ![0,c0,0,c1,c2,0] v = c0*v 1 + c1*v 3 + c2*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 4)) = c0*v 1 + c1*v 3 + c2*v 4
    ac_rfl

theorem dot_6_54 (c0 c1 c2 c3 : ℂ) (v : Fin 6→ℂ) :
    dotProduct ![0,c0,c1,0,c2,c3] v = c0*v 1 + c1*v 2 + c2*v 4 + c3*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 2 + (c2*v 4 + (c3*v 5))) = c0*v 1 + c1*v 2 + c2*v 4 + c3*v 5
    ac_rfl

theorem dot_6_57 (c0 c1 c2 c3 : ℂ) (v : Fin 6→ℂ) :
    dotProduct ![c0,0,0,c1,c2,c3] v = c0*v 0 + c1*v 3 + c2*v 4 + c3*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 4 + (c3*v 5))) = c0*v 0 + c1*v 3 + c2*v 4 + c3*v 5
    ac_rfl

theorem dot_6_5 (c0 c1 : ℂ) (v : Fin 6→ℂ) :
    dotProduct ![c0,0,c1,0,0,0] v = c0*v 0 + c1*v 2 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2) = c0*v 0 + c1*v 2
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_7_105 (c0 c1 c2 c3 : ℂ) (v : Fin 7→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,c3] v = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5 + (c3*v 6))) = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 6
    ac_rfl

theorem dot_7_37 (c0 c1 c2 : ℂ) (v : Fin 7→ℂ) :
    dotProduct ![c0,0,c1,0,0,c2,0] v = c0*v 0 + c1*v 2 + c2*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 5)) = c0*v 0 + c1*v 2 + c2*v 5
    ac_rfl

theorem dot_7_43 (c0 c1 c2 c3 : ℂ) (v : Fin 7→ℂ) :
    dotProduct ![c0,c1,0,c2,0,c3,0] v = c0*v 0 + c1*v 1 + c2*v 3 + c3*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 3 + (c3*v 5))) = c0*v 0 + c1*v 1 + c2*v 3 + c3*v 5
    ac_rfl

theorem dot_7_57 (c0 c1 c2 c3 : ℂ) (v : Fin 7→ℂ) :
    dotProduct ![c0,0,0,c1,c2,c3,0] v = c0*v 0 + c1*v 3 + c2*v 4 + c3*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 4 + (c3*v 5))) = c0*v 0 + c1*v 3 + c2*v 4 + c3*v 5
    ac_rfl

theorem dot_7_86 (c0 c1 c2 c3 : ℂ) (v : Fin 7→ℂ) :
    dotProduct ![0,c0,c1,0,c2,0,c3] v = c0*v 1 + c1*v 2 + c2*v 4 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 2 + (c2*v 4 + (c3*v 6))) = c0*v 1 + c1*v 2 + c2*v 4 + c3*v 6
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_8_105 (c0 c1 c2 c3 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,c3,0] v = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5 + (c3*v 6))) = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 6
    ac_rfl

theorem dot_8_106 (c0 c1 c2 c3 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![0,c0,0,c1,0,c2,c3,0] v = c0*v 1 + c1*v 3 + c2*v 5 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 5 + (c3*v 6))) = c0*v 1 + c1*v 3 + c2*v 5 + c3*v 6
    ac_rfl

theorem dot_8_130 (c0 c1 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,c1] v = c0*v 1 + c1*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 7) = c0*v 1 + c1*v 7
    ac_rfl

theorem dot_8_131 (c0 c1 c2 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![c0,c1,0,0,0,0,0,c2] v = c0*v 0 + c1*v 1 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 7)) = c0*v 0 + c1*v 1 + c2*v 7
    ac_rfl

theorem dot_8_149 (c0 c1 c2 c3 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![c0,0,c1,0,c2,0,0,c3] v = c0*v 0 + c1*v 2 + c2*v 4 + c3*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 4 + (c3*v 7))) = c0*v 0 + c1*v 2 + c2*v 4 + c3*v 7
    ac_rfl

theorem dot_8_169 (c0 c1 c2 c3 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,0,c3] v = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5 + (c3*v 7))) = c0*v 0 + c1*v 3 + c2*v 5 + c3*v 7
    ac_rfl

theorem dot_8_170 (c0 c1 c2 c3 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![0,c0,0,c1,0,c2,0,c3] v = c0*v 1 + c1*v 3 + c2*v 5 + c3*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 5 + (c3*v 7))) = c0*v 1 + c1*v 3 + c2*v 5 + c3*v 7
    ac_rfl

theorem dot_8_18 (c0 c1 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,0,0] v = c0*v 1 + c1*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4) = c0*v 1 + c1*v 4
    ac_rfl

theorem dot_8_213 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![c0,0,c1,0,c2,0,c3,c4] v = c0*v 0 + c1*v 2 + c2*v 4 + c3*v 6 + c4*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 4 + (c3*v 6 + (c4*v 7)))) = c0*v 0 + c1*v 2 + c2*v 4 + c3*v 6 + c4*v 7
    ac_rfl

theorem dot_8_220 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![0,0,c0,c1,c2,0,c3,c4] v = c0*v 2 + c1*v 3 + c2*v 4 + c3*v 6 + c4*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 3 + (c2*v 4 + (c3*v 6 + (c4*v 7)))) = c0*v 2 + c1*v 3 + c2*v 4 + c3*v 6 + c4*v 7
    ac_rfl

theorem dot_8_23 (c0 c1 c2 c3 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![c0,c1,c2,0,c3,0,0,0] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 4))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 4
    ac_rfl

theorem dot_8_33 (c0 c1 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![c0,0,0,0,0,c1,0,0] v = c0*v 0 + c1*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 5) = c0*v 0 + c1*v 5
    ac_rfl

theorem dot_8_37 (c0 c1 c2 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![c0,0,c1,0,0,c2,0,0] v = c0*v 0 + c1*v 2 + c2*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 5)) = c0*v 0 + c1*v 2 + c2*v 5
    ac_rfl

theorem dot_8_40 (c0 c1 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![0,0,0,c0,0,c1,0,0] v = c0*v 3 + c1*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 5) = c0*v 3 + c1*v 5
    ac_rfl

theorem dot_8_41 (c0 c1 c2 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![c0,0,0,c1,0,c2,0,0] v = c0*v 0 + c1*v 3 + c2*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 5)) = c0*v 0 + c1*v 3 + c2*v 5
    ac_rfl

theorem dot_8_44 (c0 c1 c2 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![0,0,c0,c1,0,c2,0,0] v = c0*v 2 + c1*v 3 + c2*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 3 + (c2*v 5)) = c0*v 2 + c1*v 3 + c2*v 5
    ac_rfl

theorem dot_8_45 (c0 c1 c2 c3 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![c0,0,c1,c2,0,c3,0,0] v = c0*v 0 + c1*v 2 + c2*v 3 + c3*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 3 + (c3*v 5))) = c0*v 0 + c1*v 2 + c2*v 3 + c3*v 5
    ac_rfl

theorem dot_8_57 (c0 c1 c2 c3 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![c0,0,0,c1,c2,c3,0,0] v = c0*v 0 + c1*v 3 + c2*v 4 + c3*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 4 + (c3*v 5))) = c0*v 0 + c1*v 3 + c2*v 4 + c3*v 5
    ac_rfl

theorem dot_8_66 (c0 c1 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![0,c0,0,0,0,0,c1,0] v = c0*v 1 + c1*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 6) = c0*v 1 + c1*v 6
    ac_rfl

theorem dot_8_85 (c0 c1 c2 c3 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![c0,0,c1,0,c2,0,c3,0] v = c0*v 0 + c1*v 2 + c2*v 4 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 4 + (c3*v 6))) = c0*v 0 + c1*v 2 + c2*v 4 + c3*v 6
    ac_rfl

theorem dot_8_86 (c0 c1 c2 c3 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![0,c0,c1,0,c2,0,c3,0] v = c0*v 1 + c1*v 2 + c2*v 4 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 2 + (c2*v 4 + (c3*v 6))) = c0*v 1 + c1*v 2 + c2*v 4 + c3*v 6
    ac_rfl

theorem dot_8_92 (c0 c1 c2 c3 : ℂ) (v : Fin 8→ℂ) :
    dotProduct ![0,0,c0,c1,c2,0,c3,0] v = c0*v 2 + c1*v 3 + c2*v 4 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 3 + (c2*v 4 + (c3*v 6))) = c0*v 2 + c1*v 3 + c2*v 4 + c3*v 6
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticFiniteRowEvaluation

theorem dot_9_100 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,c0,0,0,c1,c2,0,0] v = c0*v 2 + c1*v 5 + c2*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 5 + (c2*v 6)) = c0*v 2 + c1*v 5 + c2*v 6
    ac_rfl

theorem dot_9_101 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,c1,0,0,c2,c3,0,0] v = c0*v 0 + c1*v 2 + c2*v 5 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 5 + (c3*v 6))) = c0*v 0 + c1*v 2 + c2*v 5 + c3*v 6
    ac_rfl

theorem dot_9_106 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,0,c1,0,c2,c3,0,0] v = c0*v 1 + c1*v 3 + c2*v 5 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 5 + (c3*v 6))) = c0*v 1 + c1*v 3 + c2*v 5 + c3*v 6
    ac_rfl

theorem dot_9_108 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,c0,c1,0,c2,c3,0,0] v = c0*v 2 + c1*v 3 + c2*v 5 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 3 + (c2*v 5 + (c3*v 6))) = c0*v 2 + c1*v 3 + c2*v 5 + c3*v 6
    ac_rfl

theorem dot_9_10 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,0,c1,0,0,0,0,0] v = c0*v 1 + c1*v 3 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3) = c0*v 1 + c1*v 3
    ac_rfl

theorem dot_9_129 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,c1,0] v = c0*v 0 + c1*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 7) = c0*v 0 + c1*v 7
    ac_rfl

theorem dot_9_12 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,c0,c1,0,0,0,0,0] v = c0*v 2 + c1*v 3 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 3) = c0*v 2 + c1*v 3
    ac_rfl

theorem dot_9_130 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,c1,0] v = c0*v 1 + c1*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 7) = c0*v 1 + c1*v 7
    ac_rfl

theorem dot_9_131 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,c1,0,0,0,0,0,c2,0] v = c0*v 0 + c1*v 1 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 7)) = c0*v 0 + c1*v 1 + c2*v 7
    ac_rfl

theorem dot_9_132 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,c0,0,0,0,0,c1,0] v = c0*v 2 + c1*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 7) = c0*v 2 + c1*v 7
    ac_rfl

theorem dot_9_146 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,0,c2,0] v = c0*v 1 + c1*v 4 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4 + (c2*v 7)) = c0*v 1 + c1*v 4 + c2*v 7
    ac_rfl

theorem dot_9_164 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,c0,0,0,c1,0,c2,0] v = c0*v 2 + c1*v 5 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 5 + (c2*v 7)) = c0*v 2 + c1*v 5 + c2*v 7
    ac_rfl

theorem dot_9_165 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,c1,0,0,c2,0,c3,0] v = c0*v 0 + c1*v 2 + c2*v 5 + c3*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 5 + (c3*v 7))) = c0*v 0 + c1*v 2 + c2*v 5 + c3*v 7
    ac_rfl

theorem dot_9_168 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,0,c0,0,c1,0,c2,0] v = c0*v 3 + c1*v 5 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 5 + (c2*v 7)) = c0*v 3 + c1*v 5 + c2*v 7
    ac_rfl

theorem dot_9_176 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,0,0,c0,c1,0,c2,0] v = c0*v 4 + c1*v 5 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 4 + (c1*v 5 + (c2*v 7)) = c0*v 4 + c1*v 5 + c2*v 7
    ac_rfl

theorem dot_9_17 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,0,0,c1,0,0,0,0] v = c0*v 0 + c1*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 4) = c0*v 0 + c1*v 4
    ac_rfl

theorem dot_9_18 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,0,0,c1,0,0,0,0] v = c0*v 1 + c1*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 4) = c0*v 1 + c1*v 4
    ac_rfl

theorem dot_9_193 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,0,0,0,0,c1,c2,0] v = c0*v 0 + c1*v 6 + c2*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 6 + (c2*v 7)) = c0*v 0 + c1*v 6 + c2*v 7
    ac_rfl

theorem dot_9_1 (c0 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,0] v = c0*v 0 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 = c0*v 0
    ac_rfl

theorem dot_9_202 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,0,c1,0,0,c2,c3,0] v = c0*v 1 + c1*v 3 + c2*v 6 + c3*v 7 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 6 + (c3*v 7))) = c0*v 1 + c1*v 3 + c2*v 6 + c3*v 7
    ac_rfl

theorem dot_9_20 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,c0,0,c1,0,0,0,0] v = c0*v 2 + c1*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4) = c0*v 2 + c1*v 4
    ac_rfl

theorem dot_9_21 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,c1,0,c2,0,0,0,0] v = c0*v 0 + c1*v 2 + c2*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 4)) = c0*v 0 + c1*v 2 + c2*v 4
    ac_rfl

theorem dot_9_22 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,c1,0,c2,0,0,0,0] v = c0*v 1 + c1*v 2 + c2*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 2 + (c2*v 4)) = c0*v 1 + c1*v 2 + c2*v 4
    ac_rfl

theorem dot_9_256 (c0 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,0,0,0,0,0,0,c0] v = c0*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 8 = c0*v 8
    ac_rfl

theorem dot_9_257 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,0,c1] v = c0*v 0 + c1*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 8) = c0*v 0 + c1*v 8
    ac_rfl

theorem dot_9_258 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,0,0,0,0,0,0,c1] v = c0*v 1 + c1*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 8) = c0*v 1 + c1*v 8
    ac_rfl

theorem dot_9_25 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,0,c1,c2,0,0,0,0] v = c0*v 0 + c1*v 3 + c2*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 4)) = c0*v 0 + c1*v 3 + c2*v 4
    ac_rfl

theorem dot_9_26 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,0,c1,c2,0,0,0,0] v = c0*v 1 + c1*v 3 + c2*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 4)) = c0*v 1 + c1*v 3 + c2*v 4
    ac_rfl

theorem dot_9_288 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,c1] v = c0*v 5 + c1*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 8) = c0*v 5 + c1*v 8
    ac_rfl

theorem dot_9_29 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,c1,c2,c3,0,0,0,0] v = c0*v 0 + c1*v 2 + c2*v 3 + c3*v 4 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 3 + (c3*v 4))) = c0*v 0 + c1*v 2 + c2*v 3 + c3*v 4
    ac_rfl

theorem dot_9_309 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,c1,0,c2,c3,0,0,c4] v = c0*v 0 + c1*v 2 + c2*v 4 + c3*v 5 + c4*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 4 + (c3*v 5 + (c4*v 8)))) = c0*v 0 + c1*v 2 + c2*v 4 + c3*v 5 + c4*v 8
    ac_rfl

theorem dot_9_320 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,0,0,0,0,c0,0,c1] v = c0*v 6 + c1*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 6 + (c1*v 8) = c0*v 6 + c1*v 8
    ac_rfl

theorem dot_9_32 (c0 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,0,0] v = c0*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 = c0*v 5
    ac_rfl

theorem dot_9_330 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,0,c1,0,0,c2,0,c3] v = c0*v 1 + c1*v 3 + c2*v 6 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 6 + (c3*v 8))) = c0*v 1 + c1*v 3 + c2*v 6 + c3*v 8
    ac_rfl

theorem dot_9_346 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,0,c1,c2,0,c3,0,c4] v = c0*v 1 + c1*v 3 + c2*v 4 + c3*v 6 + c4*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 4 + (c3*v 6 + (c4*v 8)))) = c0*v 1 + c1*v 3 + c2*v 4 + c3*v 6 + c4*v 8
    ac_rfl

theorem dot_9_355 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,c1,0,0,0,c2,c3,0,c4] v = c0*v 0 + c1*v 1 + c2*v 5 + c3*v 6 + c4*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 5 + (c3*v 6 + (c4*v 8)))) = c0*v 0 + c1*v 1 + c2*v 5 + c3*v 6 + c4*v 8
    ac_rfl

theorem dot_9_37 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,c1,0,0,c2,0,0,0] v = c0*v 0 + c1*v 2 + c2*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 5)) = c0*v 0 + c1*v 2 + c2*v 5
    ac_rfl

theorem dot_9_385 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,0,0,0,0,0,c1,c2] v = c0*v 0 + c1*v 7 + c2*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 7 + (c2*v 8)) = c0*v 0 + c1*v 7 + c2*v 8
    ac_rfl

theorem dot_9_39 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,c1,c2,0,0,c3,0,0,0] v = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 2 + (c3*v 5))) = c0*v 0 + c1*v 1 + c2*v 2 + c3*v 5
    ac_rfl

theorem dot_9_408 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,0,c0,c1,0,0,c2,c3] v = c0*v 3 + c1*v 4 + c2*v 7 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 4 + (c2*v 7 + (c3*v 8))) = c0*v 3 + c1*v 4 + c2*v 7 + c3*v 8
    ac_rfl

theorem dot_9_416 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,0,0,0,c0,0,c1,c2] v = c0*v 5 + c1*v 7 + c2*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 5 + (c1*v 7 + (c2*v 8)) = c0*v 5 + c1*v 7 + c2*v 8
    ac_rfl

theorem dot_9_420 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,c0,0,0,c1,0,c2,c3] v = c0*v 2 + c1*v 5 + c2*v 7 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 5 + (c2*v 7 + (c3*v 8))) = c0*v 2 + c1*v 5 + c2*v 7 + c3*v 8
    ac_rfl

theorem dot_9_424 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,0,c0,0,c1,0,c2,c3] v = c0*v 3 + c1*v 5 + c2*v 7 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 5 + (c2*v 7 + (c3*v 8))) = c0*v 3 + c1*v 5 + c2*v 7 + c3*v 8
    ac_rfl

theorem dot_9_456 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,0,c0,0,0,c1,c2,c3] v = c0*v 3 + c1*v 6 + c2*v 7 + c3*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 6 + (c2*v 7 + (c3*v 8))) = c0*v 3 + c1*v 6 + c2*v 7 + c3*v 8
    ac_rfl

theorem dot_9_484 (c0 c1 c2 c3 c4 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,c0,0,0,c1,c2,c3,c4] v = c0*v 2 + c1*v 5 + c2*v 6 + c3*v 7 + c4*v 8 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 5 + (c2*v 6 + (c3*v 7 + (c4*v 8)))) = c0*v 2 + c1*v 5 + c2*v 6 + c3*v 7 + c4*v 8
    ac_rfl

theorem dot_9_52 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,c0,0,c1,c2,0,0,0] v = c0*v 2 + c1*v 4 + c2*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 4 + (c2*v 5)) = c0*v 2 + c1*v 4 + c2*v 5
    ac_rfl

theorem dot_9_53 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,c1,0,c2,c3,0,0,0] v = c0*v 0 + c1*v 2 + c2*v 4 + c3*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 4 + (c3*v 5))) = c0*v 0 + c1*v 2 + c2*v 4 + c3*v 5
    ac_rfl

theorem dot_9_57 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,0,c1,c2,c3,0,0,0] v = c0*v 0 + c1*v 3 + c2*v 4 + c3*v 5 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 3 + (c2*v 4 + (c3*v 5))) = c0*v 0 + c1*v 3 + c2*v 4 + c3*v 5
    ac_rfl

theorem dot_9_65 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,0,0,0,0,c1,0,0] v = c0*v 0 + c1*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 6) = c0*v 0 + c1*v 6
    ac_rfl

theorem dot_9_66 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,0,0,0,0,c1,0,0] v = c0*v 1 + c1*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 6) = c0*v 1 + c1*v 6
    ac_rfl

theorem dot_9_72 (c0 c1 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,0,c0,0,0,c1,0,0] v = c0*v 3 + c1*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 + (c1*v 6) = c0*v 3 + c1*v 6
    ac_rfl

theorem dot_9_74 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,0,c1,0,0,c2,0,0] v = c0*v 1 + c1*v 3 + c2*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 3 + (c2*v 6)) = c0*v 1 + c1*v 3 + c2*v 6
    ac_rfl

theorem dot_9_75 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,c1,0,c2,0,0,c3,0,0] v = c0*v 0 + c1*v 1 + c2*v 3 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 1 + (c2*v 3 + (c3*v 6))) = c0*v 0 + c1*v 1 + c2*v 3 + c3*v 6
    ac_rfl

theorem dot_9_76 (c0 c1 c2 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,c0,c1,0,0,c2,0,0] v = c0*v 2 + c1*v 3 + c2*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 2 + (c1*v 3 + (c2*v 6)) = c0*v 2 + c1*v 3 + c2*v 6
    ac_rfl

theorem dot_9_78 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,c0,c1,c2,0,0,c3,0,0] v = c0*v 1 + c1*v 2 + c2*v 3 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 1 + (c1*v 2 + (c2*v 3 + (c3*v 6))) = c0*v 1 + c1*v 2 + c2*v 3 + c3*v 6
    ac_rfl

theorem dot_9_85 (c0 c1 c2 c3 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![c0,0,c1,0,c2,0,c3,0,0] v = c0*v 0 + c1*v 2 + c2*v 4 + c3*v 6 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 0 + (c1*v 2 + (c2*v 4 + (c3*v 6))) = c0*v 0 + c1*v 2 + c2*v 4 + c3*v 6
    ac_rfl

theorem dot_9_8 (c0 : ℂ) (v : Fin 9→ℂ) :
    dotProduct ![0,0,0,c0,0,0,0,0,0] v = c0*v 3 := by
  simp only [Matrix.cons_dotProduct,Matrix.dotProduct_of_isEmpty,zero_mul,add_zero,zero_add]
  all_goals
    change c0*v 3 = c0*v 3
    ac_rfl

end QuantitativeArithmeticFiniteRowEvaluation
end
end
end
