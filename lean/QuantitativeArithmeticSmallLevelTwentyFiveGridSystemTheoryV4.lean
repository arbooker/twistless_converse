module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveGridRamanujanRowsV1
public import QuantitativeArithmeticSmallLevelTwentyFiveSelectedWordsTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive.GridSystem. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveGridSystemV1 -/
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.GridSystem
open Complex Matrix SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
open QuantitativeArithmeticSmallLevelTwentyFive.GridRamanujan

inductive RowKind where
  | group : Fin 45 → RowKind
  | taylor : Fin 47 → RowKind
  | entire : Fin 4 → RowKind
  | center : Fin 3 → RowKind
  | hecke : Fin 51 → RowKind
  deriving DecidableEq

def rowKind : Fin 150 → RowKind :=
  ![.center 0,.group 0,.group 1,.group 2,.center 1,.group 3,.group 4,.group 5,.group 6,.group 7,.group 8,.center 2,.group 9,.group 10,.group 11,.entire 0,.group 12,.taylor 0,.group 13,.group 14,.group 15,.group 16,.group 17,.group 18,.group 19,.group 20,.group 21,.group 22,.group 23,.group 24,.group 25,.group 26,.group 27,.group 28,.group 29,.group 30,.group 31,.group 32,.group 33,.group 34,.group 35,.group 36,.group 37,.group 38,.group 39,.group 40,.group 41,.group 42,.group 43,.group 44,.taylor 1,.taylor 2,.taylor 3,.taylor 4,.taylor 5,.taylor 6,.taylor 7,.taylor 8,.entire 1,.taylor 9,.taylor 10,.hecke 0,.entire 2,.hecke 1,.hecke 2,.hecke 3,.hecke 4,.taylor 11,.taylor 12,.taylor 13,.taylor 14,.taylor 15,.taylor 16,.entire 3,.hecke 5,.hecke 6,.taylor 17,.taylor 18,.taylor 19,.taylor 20,.hecke 7,.taylor 21,.hecke 8,.taylor 22,.taylor 23,.taylor 24,.taylor 25,.taylor 26,.taylor 27,.taylor 28,.hecke 9,.hecke 10,.hecke 11,.hecke 12,.hecke 13,.taylor 29,.taylor 30,.taylor 31,.taylor 32,.taylor 33,.taylor 34,.hecke 14,.hecke 15,.hecke 16,.hecke 17,.hecke 18,.hecke 19,.hecke 20,.hecke 21,.hecke 22,.hecke 23,.hecke 24,.hecke 25,.hecke 26,.hecke 27,.hecke 28,.hecke 29,.hecke 30,.hecke 31,.taylor 35,.hecke 32,.taylor 36,.taylor 37,.taylor 38,.hecke 33,.taylor 39,.hecke 34,.hecke 35,.hecke 36,.hecke 37,.hecke 38,.hecke 39,.hecke 40,.taylor 40,.hecke 41,.hecke 42,.hecke 43,.hecke 44,.taylor 41,.taylor 42,.taylor 43,.hecke 45,.hecke 46,.hecke 47,.taylor 44,.hecke 48,.hecke 49,.taylor 45,.hecke 50,.taylor 46]

def assemble (G : Fin 45 → ℂ) (T : Fin 47 → ℂ) (E : Fin 4 → ℂ)
    (C : Fin 3 → ℂ) (H : Fin 51 → ℂ) (i : Fin 150) : ℂ :=
  match rowKind i with
  | .group j => G j
  | .taylor j => T j
  | .entire j => E j
  | .center j => C j
  | .hecke j => H j

def leadingRows (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v : Fin 150 → ℂ) : Fin 150 → ℂ :=
  assemble (fun i => v (gridIndex (groupSource i))-groupCoefficient m i 0 s*v (gridIndex (groupPartner i)))
    (fun i => plusRows v i-rowCoefficient (2*m) f ε i 0 s*minusRows v i) (entireRows v)
    (fun i => v (gridIndex (infinitySource i)))
    (selectedHeckeRows m f s v)

def shiftRows (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (v : Fin 150 → ℂ) : Fin 150 → ℂ :=
  assemble (fun i => groupCoefficient m i (n+1) s*v (gridIndex (groupPartner i)))
    (fun i => rowCoefficient (2*m) f ε i (n+1) s*minusRows v i) 0 0 0

def leadingLinear (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : (Fin 150 → ℂ) →ₗ[ℂ] (Fin 150 → ℂ) where
  toFun := leadingRows m f ε s
  map_add' := by
    intro v w
    funext i
    cases hi : rowKind i <;>
      simp [leadingRows,assemble,hi,plusRows,minusRows,entireRows,sumRow,heckeRow,selectedHeckeRows,fiveRow,Finset.sum_add_distrib] <;> (try split_ifs) <;> ring
  map_smul' := by
    intro a v
    funext i
    cases hi : rowKind i <;>
      simp [leadingRows,assemble,hi,plusRows,minusRows,entireRows,sumRow,heckeRow,selectedHeckeRows,fiveRow,smul_eq_mul,← Finset.mul_sum] <;> (try split_ifs) <;> ring

def shiftLinear (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : (Fin 150 → ℂ) →ₗ[ℂ] (Fin 150 → ℂ) where
  toFun := shiftRows m f ε n s
  map_add' := by
    intro v w
    funext i
    cases hi : rowKind i <;>
      simp [shiftRows,assemble,hi,minusRows,sumRow,Finset.sum_add_distrib] <;> (try split_ifs) <;> ring
  map_smul' := by
    intro a v
    funext i
    cases hi : rowKind i <;>
      simp [shiftRows,assemble,hi,minusRows,sumRow,smul_eq_mul,← Finset.mul_sum] <;> (try split_ifs) <;> ring

def leadingMatrix (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : Matrix (Fin 150) (Fin 150) ℂ :=
  (leadingLinear m f ε s).toMatrix'
def shiftMatrix (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin 150) (Fin 150) ℂ :=
  (shiftLinear m f ε n s).toMatrix'

theorem leadingMatrix_mulVec (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v : Fin 150 → ℂ) :
    leadingMatrix m f ε s *ᵥ v=leadingRows m f ε s v := LinearMap.toMatrix'_mulVec _ _
theorem shiftMatrix_mulVec (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (v : Fin 150 → ℂ) :
    shiftMatrix m f ε n s *ᵥ v=shiftRows m f ε n s v := LinearMap.toMatrix'_mulVec _ _

#print axioms leadingMatrix_mulVec
#print axioms shiftMatrix_mulVec
end QuantitativeArithmeticSmallLevelTwentyFive.GridSystem
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveGridEntriesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.GridSystem
open Complex Matrix
open QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
open QuantitativeArithmeticSmallLevelTwentyFive.GridRamanujan

theorem leadingMatrix_apply (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i j : Fin 150) :
    leadingMatrix m f ε s i j=leadingRows m f ε s (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _
theorem shiftMatrix_apply (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (i j : Fin 150) :
    shiftMatrix m f ε n s i j=shiftRows m f ε n s (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _

theorem leadingMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε x : ℂ) (i j : Fin 150) :
    AnalyticAt ℂ (fun s => leadingMatrix m f ε s i j) x := by
  simp only [leadingMatrix_apply]
  cases hi : rowKind i with
  | group a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const.sub ((groupCoefficient_analytic m a 0 x).mul analyticAt_const)
  | taylor a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const.sub ((rowCoefficient_analytic (2*m) f ε a 0 x).mul analyticAt_const)
  | entire a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const
  | center a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const
  | hecke a =>
    simp only [leadingRows,assemble,hi,selectedHeckeRows]
    split_ifs with hbad
    · exact analyticAt_const
    · have hpos : 0<(heckeSpecs a).1 := by
        rcases heckeSpecs_valid a with h|h|h <;> omega
      have hp := SmallLevelTaylor.hecke_parameter_analytic hpos m x
      simp only [heckeRow]
      exact (analyticAt_const.sub ((analyticAt_const.mul hp).mul analyticAt_const)).add
        ((hp.pow 2).mul analyticAt_const)

theorem shiftMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (x : ℂ) (i j : Fin 150) :
    AnalyticAt ℂ (fun s => shiftMatrix m f ε n s i j) x := by
  simp only [shiftMatrix_apply]
  cases hi : rowKind i with
  | group a =>
    simp only [shiftRows,assemble,hi]
    exact (groupCoefficient_analytic m a (n+1) x).mul analyticAt_const
  | taylor a =>
    simp only [shiftRows,assemble,hi]
    exact (rowCoefficient_analytic (2*m) f ε a (n+1) x).mul analyticAt_const
  | entire a => simp only [shiftRows,assemble,hi,Pi.zero_apply]; exact analyticAt_const
  | center a => simp only [shiftRows,assemble,hi,Pi.zero_apply]; exact analyticAt_const
  | hecke a => simp only [shiftRows,assemble,hi,Pi.zero_apply]; exact analyticAt_const

#print axioms leadingMatrix_analytic
#print axioms shiftMatrix_analytic
end QuantitativeArithmeticSmallLevelTwentyFive.GridSystem
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveGridOriginalSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.GridSystem
open Complex Matrix Set SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
open QuantitativeArithmeticSmallLevelTwentyFive.GridRamanujan

/-- The selected positive generic square system have actual original-input Taylor
identities. Rank and specialization are separate from this analytic assembly. -/
theorem original_matrix_system {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε) :
    ∃ B : ℝ, ∃ error : ℕ → ℂ → Fin 150 → ℂ,
      (∀ i : Fin 150, ∀ s : ℂ, B<s.re → AnalyticAt ℂ (fun z => gridVector (2*m) f z i) s) ∧
      (∀ M : ℕ, ∀ i : Fin 150, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (fun z => error M z i) s) ∧
      ∀ M : ℕ, ∀ s : ℂ, B<s.re →
        leadingMatrix m f ε s *ᵥ gridVector (2*m) f s=
          error M s+∑ n∈Finset.range M,
            shiftMatrix m f ε n s *ᵥ gridVector (2*m) f (s+((n:ℂ)+1)) := by
  obtain ⟨BG,errG,hG⟩ := original_group_system hf
  choose bT hT using fun i : Fin 47 => original_taylor_rows hf ε hlaw i
  obtain ⟨hRE,BR,hR⟩ := GridRamanujan.original_entire_rows (by omega : 0<2*m) hf
  choose CE hCED bC hC using fun i : Fin 3 => original_selected_entire hm hf i
  have hCE (i : Fin 3) (s : ℂ) : AnalyticAt ℂ (CE i) s := (hCED i).analyticAt s
  have hCGrid (i : Fin 3) (s : ℂ) (hs : bC i<s.re) :
      CE i s=gridVector (2*m) f s (gridIndex (infinitySource i)) := by
    simpa only [gridVector_index,grid,Nat.cast_ofNat] using hC i s hs
  obtain ⟨BH,hH⟩ := original_selected_hecke hf
  obtain ⟨BF,hF⟩ := original_common_halfplane hf
  let BT : ℝ := Finset.univ.sup' Finset.univ_nonempty bT
  let BC : ℝ := Finset.univ.sup' Finset.univ_nonempty bC
  let bounds : Fin 6 → ℝ := ![BG,BT,BR,BC,BH,BF]
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty bounds
  have hb (i : Fin 6) : bounds i≤B := Finset.le_sup' bounds (Finset.mem_univ i)
  have hBG : BG≤B := by simpa only [bounds,Matrix.cons_val_zero] using hb 0
  have hBT (i : Fin 47) : bT i≤B :=
    (show bT i≤BT from Finset.le_sup' bT (Finset.mem_univ i)).trans (by simpa only [bounds,Matrix.cons_val] using hb 1)
  have hBR : BR≤B := by simpa [bounds] using hb 2
  have hBC (i : Fin 3) : bC i≤B :=
    (show bC i≤BC from Finset.le_sup' bC (Finset.mem_univ i)).trans (by simpa only [bounds,Matrix.cons_val] using hb 3)
  have hBH : BH≤B := by simpa only [bounds,Matrix.cons_val] using hb 4
  have hBF : BF≤B := by simpa [bounds] using hb 5
  let error : ℕ → ℂ → Fin 150 → ℂ := fun M s =>
    assemble (fun i => errG i M s) (fun i => rowError (2*m) f ε i M s)
      (fun i => ramanujanEntire 25 (2*m) f (GridRamanujan.entireSpecs i) s)
      (fun i => CE i s) 0
  refine ⟨B,error,?_,?_,?_⟩
  · intro i s hs
    exact (hF ((i.val:ℝ)/150) s (lt_of_le_of_lt hBF hs)).1
  · intro M i s hs
    have hg' (j : Fin 45) : AnalyticAt ℂ (errG j M) s := by
      apply (hG j M).1 s
      change BG-((M:ℝ)+1)<s.re
      linarith
    have ht' (j : Fin 47) : AnalyticAt ℂ (rowError (2*m) f ε j M) s := by
      apply (hT j M).1 s
      change bT j-((M:ℝ)+1)<s.re
      linarith [hBT j]
    cases hi : rowKind i with
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
    cases hi : rowKind i with
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
        Finset.sum_const_zero,add_zero] using (hCGrid j s (lt_of_le_of_lt (hBC j) hs)).symm
    | hecke j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,Pi.zero_apply,
        Finset.sum_const_zero,add_zero] using
          hH j s (lt_of_le_of_lt hBH hs)

#print axioms original_matrix_system
end QuantitativeArithmeticSmallLevelTwentyFive.GridSystem
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveGridLaurentV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.GridSystem
open Complex SmallLevelTaylor FinitenessNormalizedTwistProduct
open QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
open QuantitativeArithmeticSmallLevelTwentyFive.GridRamanujan

def threePrimeMonomial (e : ℤ×ℤ×ℤ) (x y z : ℂ) : ℂ := x^e.1*y^e.2.1*z^e.2.2
def primeParameter (p m : ℕ) (s : ℂ) : ℂ := (p:ℂ)^(s-(m:ℂ))
def phaseRoot (m : ℕ) (ε : ℂ) : ℂ := ε*I^(2*m)

theorem real_three_prime_power (r : ℝ) (e : ℤ×ℤ×ℤ)
    (hr : r=(2:ℝ)^e.1*(3:ℝ)^e.2.1*(5:ℝ)^e.2.2) (s : ℂ) :
    (r:ℂ)^s=threePrimeMonomial e ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) := by
  rw [hr,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  simp only [Complex.ofReal_zpow]
  rw [QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic.positive_zpow_cpow (by norm_num : (0:ℝ)<2),
    QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic.positive_zpow_cpow (by norm_num : (0:ℝ)<3),
    QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic.positive_zpow_cpow (by norm_num : (0:ℝ)<5)]
  rfl

def groupPowers : Fin 45 → ℤ×ℤ×ℤ := ![(0,2,0),(2,0,0),(0,0,0),(-2,0,0),(-2,0,0),(0,2,0),(0,-2,0),(2,0,0),(0,0,0),(0,2,0),(0,0,0),(0,2,0),(-2,0,0),(2,2,0),(2,2,0),(0,2,0),(2,0,0),(-2,2,0),(2,-2,0),(-2,0,0),(0,-2,0),(-2,-2,0),(-2,-2,0),(-2,0,0),(2,0,0),(2,2,0),(0,2,0),(2,0,0),(-2,2,0),(-2,-2,0),(-2,0,0),(2,-2,0),(0,0,0),(-2,2,0),(2,0,0),(0,2,0),(2,2,0),(2,2,0),(0,2,0),(-2,2,0),(2,-2,0),(0,-2,0),(-2,-2,0),(-2,-2,0),(2,2,0)]
theorem group_rate_certificate (i : Fin 45) :
    groupRate i=(2:ℝ)^(groupPowers i).1*(3:ℝ)^(groupPowers i).2.1*(5:ℝ)^(groupPowers i).2.2 := by
  fin_cases i <;> norm_num [groupRate,groupPowers,gC,gD,groupCenter,groupSource,groupWord,matrices]

def symbolicGroup (X Y Z : ℂ) (i : Fin 45) : ℂ := threePrimeMonomial (groupPowers i) X Y Z

theorem groupCoefficient_laurent (m : ℕ) (s : ℂ) (i : Fin 45) :
    groupCoefficient m i 0 s=symbolicGroup
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 5 m s) i := by
  simp only [groupCoefficient,Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one]
  rw [real_three_prime_power _ _ (group_rate_certificate i)]
  rfl

def taylorPowers : Fin 47 → ℤ×ℤ×ℤ := ![(-2,-2,-2),(-2,-2,0),(-2,2,-2),(-2,2,-2),(0,-2,0),(2,-2,0),(2,-2,0),(-2,-2,2),(-2,-2,2),(0,0,0),(0,0,0),(-2,0,-2),(-2,0,-2),(0,0,-2),(0,0,-2),(2,0,-2),(2,0,-2),(-2,0,0),(0,-2,0),(0,-2,0),(-2,0,0),(-2,-2,0),(-2,-2,0),(0,0,-2),(0,0,-2),(2,0,-2),(2,0,-2),(0,0,-2),(0,0,-2),(-2,0,-2),(-2,0,-2),(-2,2,-2),(-2,2,-2),(0,-2,-2),(0,-2,-2),(0,0,-2),(0,-2,-2),(-2,0,-2),(0,0,-2),(2,-2,-2),(-2,-2,-2),(2,-2,-2),(-2,0,-2),(-2,-2,0),(0,-2,-2),(-2,-2,-2),(-2,-2,0)]
def symbolicTaylor (χ X Y Z : ℂ) (i : Fin 47) : ℂ :=
  χ*threePrimeMonomial (taylorPowers i) X Y Z

theorem taylor_rate_certificate (i : Fin 47) :
    (rowL i:ℝ)*((rowT i:ℝ)/150)^2=
      (2:ℝ)^(taylorPowers i).1*(3:ℝ)^(taylorPowers i).2.1*(5:ℝ)^(taylorPowers i).2.2 := by
  fin_cases i <;> norm_num [rowL,rowQ,rowT,taylorPowers]

theorem taylor_root_scalar (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 47) :
    root 25 f (rowQ i)*ε*I^(2*m)=phaseRoot m ε := by
  rw [QuantitativeArithmeticSmallLevelTwentyFive.twist_root_one,one_mul]
  rfl

theorem taylorCoefficient_laurent (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (i : Fin 47) :
    rowCoefficient (2*m) f ε i 0 s=symbolicTaylor (phaseRoot m ε)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 5 m s) i := by
  have hex : s-((2*m:ℕ):ℂ)/2=s-(m:ℂ) := by push_cast; ring
  simp only [rowCoefficient,taylorRowScalar,pow_zero,Ring.choose_zero_right,mul_one,hex,taylor_root_scalar]
  rw [real_three_prime_power _ _ (taylor_rate_certificate i)]
  rfl

#print axioms groupCoefficient_laurent
#print axioms taylorCoefficient_laurent
end QuantitativeArithmeticSmallLevelTwentyFive.GridSystem
end
end
