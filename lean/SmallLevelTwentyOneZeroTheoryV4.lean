module

public import SmallLevelFiniteHeckeStepV1
public import SmallLevelTwentyOneThreeTheoryV4

/-! Consolidated chapter: SmallLevelTwentyOneZero. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyOneZeroDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneZero
open Matrix UpperHalfPlane SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

def kernel : Fin 24 → SL(2,ℤ)
  | 0 => ⟨!![1,1;0,1],by decide⟩
  | 1 => ⟨!![1,0;21,1],by decide⟩
  | 2 => ⟨!![2,-1;-21,11],by decide⟩
  | 3 => ⟨!![5,-2;-42,17],by decide⟩
  | 4 => ⟨!![5,2;42,17],by decide⟩
  | 5 => ⟨!![43,6;-294,-41],by decide⟩
  | 6 => ⟨!![85,24;-294,-83],by decide⟩
  | 7 => ⟨!![1,0;-21,1],by decide⟩
  | 8 => ⟨!![1,-1;0,1],by decide⟩
  | 9 => ⟨!![11,1;21,2],by decide⟩
  | 10 => ⟨!![17,2;42,5],by decide⟩
  | 11 => ⟨!![17,-2;-42,5],by decide⟩
  | 12 => ⟨!![41,-14;126,-43],by decide⟩
  | 13 => ⟨!![83,-14;504,-85],by decide⟩
  | 14 => ⟨!![85,-71;-504,421],by decide⟩
  | 15 => ⟨!![421,24;1491,85],by decide⟩
  | 16 => ⟨!![293,-339;1344,-1555],by decide⟩
  | 17 => ⟨!![1555,64;-7119,-293],by decide⟩
  | 18 => ⟨!![293,-247;-1344,1133],by decide⟩
  | 19 => ⟨!![1133,64;5187,293],by decide⟩
  | 20 => ⟨!![379,-459;2184,-2645],by decide⟩
  | 21 => ⟨!![2645,104;-9639,-379],by decide⟩
  | 22 => ⟨!![391,-283;-105,76],by decide⟩
  | _ => ⟨!![76,5;5943,391],by decide⟩

def knownWord : Fin 15 → List (Fin 24 × ℤ)
  | 0 => [(0,-3), (12,1), (0,-3)]
  | 1 => [(8,1), (12,4), (8,1)]
  | 2 => [(8,1), (10,-1), (9,1), (7,1), (10,1), (9,-1), (8,2)]
  | 3 => [(6,-1), (8,1), (9,1), (10,-1), (12,-1), (10,1), (9,-1)]
  | 4 => [(8,1), (11,-1), (8,1), (9,1), (11,1), (7,-1), (9,-1), (0,-3)]
  | 5 => [(15,1), (7,1), (12,1), (8,1)]
  | 6 => [(8,-1), (7,-1), (17,-1), (18,1), (8,2)]
  | 7 => [(9,1), (10,-1), (12,-1), (10,1), (9,-1), (8,-1), (6,-1), (8,1)]
  | 8 => [(0,-19), (10,1), (9,-1)]
  | 9 => [(0,-91), (8,2), (9,-1)]
  | 10 => [(0,-4), (9,1), (7,1), (0,-3)]
  | 11 => [(0,-4), (9,1), (10,-1), (12,-1)]
  | 12 => [(0,-3), (10,-1), (9,1), (8,1)]
  | 13 => [(0,-3), (7,-1), (10,-1), (9,1), (7,1)]
  | _ => [(5,1), (10,-1), (9,1), (23,-1), (1,4)]

def target : Fin 15 → SL(2,ℤ)
  | 0 => ⟨!![337,-1126;-126,421],by decide⟩
  | 1 => ⟨!![337,-450;-504,673],by decide⟩
  | 2 => ⟨!![379,-996;-336,883],by decide⟩
  | 3 => ⟨!![379,-249;-1344,883],by decide⟩
  | 4 => ⟨!![293,-988;-336,1133],by decide⟩
  | 5 => ⟨!![379,-509;1344,-1805],by decide⟩
  | 6 => ⟨!![379,-1078;546,-1553],by decide⟩
  | 7 => ⟨!![1471,-1046;2184,-1553],by decide⟩
  | 8 => ⟨!![-391,242;21,-13],by decide⟩
  | 9 => ⟨!![1955,-1024;-21,11],by decide⟩
  | 10 => ⟨!![74,-229;-21,65],by decide⟩
  | 11 => ⟨!![349,-113;-105,34],by decide⟩
  | 12 => ⟨!![328,-303;-105,97],by decide⟩
  | 13 => ⟨!![307,-38;-105,13],by decide⟩
  | _ => ⟨!![146,25;-987,-169],by decide⟩

def stageSize : Fin 15 → ℕ
  | 0 => 14
  | 1 => 14
  | 2 => 16
  | 3 => 16
  | 4 => 18
  | 5 => 18
  | 6 => 20
  | 7 => 20
  | 8 => 22
  | 9 => 22
  | 10 => 22
  | 11 => 22
  | 12 => 22
  | 13 => 22
  | _ => 24

def wordSign : Fin 15 → SL(2,ℤ)
  | 0 => -1
  | 1 => 1
  | 2 => 1
  | 3 => -1
  | 4 => -1
  | 5 => -1
  | 6 => -1
  | 7 => -1
  | 8 => -1
  | 9 => 1
  | 10 => 1
  | 11 => -1
  | 12 => 1
  | 13 => 1
  | _ => -1

def wordEval (i : Fin 15) : SL(2,ℤ) := ((knownWord i).map (fun p => kernel p.1 ^ p.2)).prod

theorem word_checked (i : Fin 15) : target i=wordSign i*wordEval i := by
  fin_cases i <;> decide

theorem word_bound : ∀ i : Fin 15, ∀ p∈knownWord i, p.1.val<stageSize i := by decide

theorem target_mem (K : Subgroup SL(2,ℤ)) (hz : -1∈K) (i : Fin 15)
    (hk : ∀ j : Fin 24, j.val<stageSize i → kernel j∈K) : target i∈K := by
  rw [word_checked]
  apply K.mul_mem
  · have hsign : ∀ i : Fin 15, wordSign i=1 ∨ wordSign i= -1 := by decide
    rcases hsign i with h|h
    · rw [h]; exact K.one_mem
    · rw [h]; exact hz
  · apply K.list_prod_mem
    intro x hx
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    exact K.zpow_mem (hk p.1 (word_bound i p hp)) p.2

def twoBranch : Fin 3 → GL (Fin 2) ℝ
  | 0 => QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeInfinity
  | 1 => QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeFinite 0
  | _ => QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeFinite 1

def fiveBranch : Fin 6 → GL (Fin 2) ℝ
  | 0 => SmallLevelGoodHeckeFive.heckeInfinity
  | 1 => SmallLevelGoodHeckeFive.heckeFinite 0
  | 2 => SmallLevelGoodHeckeFive.heckeFinite 1
  | 3 => SmallLevelGoodHeckeFive.heckeFinite 2
  | 4 => SmallLevelGoodHeckeFive.heckeFinite 3
  | _ => SmallLevelGoodHeckeFive.heckeFinite 4

def stepB0 : SL(2,ℤ) := ⟨!![-337,563;252,-421],by decide⟩

def stepGamma0 : Fin 3 → SL(2,ℤ)
  | 0 => ⟨!![-337,1126;126,-421],by decide⟩
  | 1 => ⟨!![-337,450;504,-673],by decide⟩
  | _ => ⟨!![-85,71;504,-421],by decide⟩

def stepPerm0 : Equiv.Perm (Fin 3) :=
  ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩

theorem stepBranches0 (i : Fin 3) :
    twoBranch i*SpecialLinearGroup.mapGL ℝ stepB0=
      SpecialLinearGroup.mapGL ℝ (stepGamma0 i)*twoBranch (stepPerm0 i) := by
  fin_cases i <;>
    apply Units.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [twoBranch,stepB0,stepGamma0,stepPerm0,
      QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeInfinity,
      QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeFinite,
      SmallLevelGoodHeckeFive.heckeInfinity,SmallLevelGoodHeckeFive.heckeFinite,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Fin.sum_univ_two]

def stepB1 : SL(2,ℤ) := ⟨!![-379,498;672,-883],by decide⟩

def stepGamma1 : Fin 3 → SL(2,ℤ)
  | 0 => ⟨!![-379,996;336,-883],by decide⟩
  | 1 => ⟨!![-379,249;1344,-883],by decide⟩
  | _ => ⟨!![293,-339;1344,-1555],by decide⟩

def stepPerm1 : Equiv.Perm (Fin 3) :=
  ⟨![0, 1, 2], ![0, 1, 2], by decide, by decide⟩

theorem stepBranches1 (i : Fin 3) :
    twoBranch i*SpecialLinearGroup.mapGL ℝ stepB1=
      SpecialLinearGroup.mapGL ℝ (stepGamma1 i)*twoBranch (stepPerm1 i) := by
  fin_cases i <;>
    apply Units.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [twoBranch,stepB1,stepGamma1,stepPerm1,
      QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeInfinity,
      QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeFinite,
      SmallLevelGoodHeckeFive.heckeInfinity,SmallLevelGoodHeckeFive.heckeFinite,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Fin.sum_univ_two]

def stepB2 : SL(2,ℤ) := ⟨!![-293,494;672,-1133],by decide⟩

def stepGamma2 : Fin 3 → SL(2,ℤ)
  | 0 => ⟨!![-293,988;336,-1133],by decide⟩
  | 1 => ⟨!![-293,247;1344,-1133],by decide⟩
  | _ => ⟨!![379,-509;1344,-1805],by decide⟩

def stepPerm2 : Equiv.Perm (Fin 3) :=
  ⟨![0, 1, 2], ![0, 1, 2], by decide, by decide⟩

theorem stepBranches2 (i : Fin 3) :
    twoBranch i*SpecialLinearGroup.mapGL ℝ stepB2=
      SpecialLinearGroup.mapGL ℝ (stepGamma2 i)*twoBranch (stepPerm2 i) := by
  fin_cases i <;>
    apply Units.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [twoBranch,stepB2,stepGamma2,stepPerm2,
      QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeInfinity,
      QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeFinite,
      SmallLevelGoodHeckeFive.heckeInfinity,SmallLevelGoodHeckeFive.heckeFinite,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Fin.sum_univ_two]

def stepB3 : SL(2,ℤ) := ⟨!![379,-539;1092,-1553],by decide⟩

def stepGamma3 : Fin 3 → SL(2,ℤ)
  | 0 => ⟨!![379,-1078;546,-1553],by decide⟩
  | 1 => ⟨!![379,-459;2184,-2645],by decide⟩
  | _ => ⟨!![1471,-1046;2184,-1553],by decide⟩

def stepPerm3 : Equiv.Perm (Fin 3) :=
  ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩

theorem stepBranches3 (i : Fin 3) :
    twoBranch i*SpecialLinearGroup.mapGL ℝ stepB3=
      SpecialLinearGroup.mapGL ℝ (stepGamma3 i)*twoBranch (stepPerm3 i) := by
  fin_cases i <;>
    apply Units.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [twoBranch,stepB3,stepGamma3,stepPerm3,
      QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeInfinity,
      QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeFinite,
      SmallLevelGoodHeckeFive.heckeInfinity,SmallLevelGoodHeckeFive.heckeFinite,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Fin.sum_univ_two]

def stepB4 : SL(2,ℤ) := ⟨!![-391,242;21,-13],by decide⟩

def stepGamma4 : Fin 6 → SL(2,ℤ)
  | 0 => ⟨!![-1955,1024;21,-11],by decide⟩
  | 1 => ⟨!![-391,283;105,-76],by decide⟩
  | 2 => ⟨!![-74,229;21,-65],by decide⟩
  | 3 => ⟨!![-349,113;105,-34],by decide⟩
  | 4 => ⟨!![-328,303;105,-97],by decide⟩
  | _ => ⟨!![-307,38;105,-13],by decide⟩

def stepPerm4 : Equiv.Perm (Fin 6) :=
  ⟨![3, 4, 0, 2, 5, 1], ![2, 5, 3, 0, 1, 4], by decide, by decide⟩

theorem stepBranches4 (i : Fin 6) :
    fiveBranch i*SpecialLinearGroup.mapGL ℝ stepB4=
      SpecialLinearGroup.mapGL ℝ (stepGamma4 i)*fiveBranch (stepPerm4 i) := by
  fin_cases i <;>
    apply Units.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [fiveBranch,stepB4,stepGamma4,stepPerm4,
      QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeInfinity,
      QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeFinite,
      SmallLevelGoodHeckeFive.heckeInfinity,SmallLevelGoodHeckeFive.heckeFinite,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Fin.sum_univ_two]

#print axioms word_checked
#print axioms target_mem
#print axioms stepBranches0
#print axioms stepBranches1
#print axioms stepBranches2
#print axioms stepBranches3
#print axioms stepBranches4
end SmallLevelTwentyOneZero
end
end

/-! ## SmallLevelTwentyOneZeroStepsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneZero
open Matrix UpperHalfPlane SmallLevelGenerators
open scoped MatrixGroups ModularForm

theorem step0 (F : ℍ → ℂ) (k : ℤ) 
    (he : QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeTwo k F=0)
    (hz : F ∣[k] (-1:SL(2,ℤ))=F)
    (hk : ∀ j : Fin 24, j.val<14 → F ∣[k] kernel j=F) :
    F ∣[k] kernel 14=F := by
  let K := slashStabilizer k F
  have hknown (j : Fin 15) (hj : stageSize j=14) : F ∣[k] target j=F := by
    apply target_mem K hz j
    intro i hi
    apply hk i
    simpa only [hj] using hi
  have hB : (0:ℂ)=0 ∨ F ∣[k] stepB0=F := Or.inl rfl
  have hh : F ∣[k] stepGamma0 2=F := by
    refine SmallLevelFiniteHeckeStep.one_missing F k twoBranch stepB0 stepGamma0
      stepPerm0 2 (0:ℂ) ?_ hB (stepBranches0) ?_
    · simpa [twoBranch,Fin.sum_univ_succ,QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeTwo,add_assoc] using he
    · intro i hi
      fin_cases i
      · have hx : stepGamma0 0=(-1)*target 0 := by decide
        change F ∣[k] stepGamma0 0=F
        rw [hx]
        exact K.mul_mem hz (hknown 0 (by decide))
      · have hx : stepGamma0 1=(-1)*target 1 := by decide
        change F ∣[k] stepGamma0 1=F
        rw [hx]
        exact K.mul_mem hz (hknown 1 (by decide))
      · exact (hi rfl).elim
  have hx : kernel 14=(-1)*stepGamma0 2 := by decide
  rw [hx]
  exact K.mul_mem hz hh

#print axioms step0

theorem step1 (F : ℍ → ℂ) (k : ℤ) 
    (he : QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeTwo k F=0)
    (hz : F ∣[k] (-1:SL(2,ℤ))=F)
    (hk : ∀ j : Fin 24, j.val<16 → F ∣[k] kernel j=F) :
    F ∣[k] kernel 16=F := by
  let K := slashStabilizer k F
  have hknown (j : Fin 15) (hj : stageSize j=16) : F ∣[k] target j=F := by
    apply target_mem K hz j
    intro i hi
    apply hk i
    simpa only [hj] using hi
  have hB : (0:ℂ)=0 ∨ F ∣[k] stepB1=F := Or.inl rfl
  have hh : F ∣[k] stepGamma1 2=F := by
    refine SmallLevelFiniteHeckeStep.one_missing F k twoBranch stepB1 stepGamma1
      stepPerm1 2 (0:ℂ) ?_ hB (stepBranches1) ?_
    · simpa [twoBranch,Fin.sum_univ_succ,QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeTwo,add_assoc] using he
    · intro i hi
      fin_cases i
      · have hx : stepGamma1 0=(-1)*target 2 := by decide
        change F ∣[k] stepGamma1 0=F
        rw [hx]
        exact K.mul_mem hz (hknown 2 (by decide))
      · have hx : stepGamma1 1=(-1)*target 3 := by decide
        change F ∣[k] stepGamma1 1=F
        rw [hx]
        exact K.mul_mem hz (hknown 3 (by decide))
      · exact (hi rfl).elim
  exact hh

#print axioms step1

theorem step2 (F : ℍ → ℂ) (k : ℤ) 
    (he : QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeTwo k F=0)
    (hz : F ∣[k] (-1:SL(2,ℤ))=F)
    (hk : ∀ j : Fin 24, j.val<18 → F ∣[k] kernel j=F) :
    F ∣[k] kernel 18=F := by
  let K := slashStabilizer k F
  have hknown (j : Fin 15) (hj : stageSize j=18) : F ∣[k] target j=F := by
    apply target_mem K hz j
    intro i hi
    apply hk i
    simpa only [hj] using hi
  have hB : (0:ℂ)=0 ∨ F ∣[k] stepB2=F := Or.inl rfl
  have hh : F ∣[k] stepGamma2 1=F := by
    refine SmallLevelFiniteHeckeStep.one_missing F k twoBranch stepB2 stepGamma2
      stepPerm2 1 (0:ℂ) ?_ hB (stepBranches2) ?_
    · simpa [twoBranch,Fin.sum_univ_succ,QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeTwo,add_assoc] using he
    · intro i hi
      fin_cases i
      · have hx : stepGamma2 0=(-1)*target 4 := by decide
        change F ∣[k] stepGamma2 0=F
        rw [hx]
        exact K.mul_mem hz (hknown 4 (by decide))
      · exact (hi rfl).elim
      · exact hknown 5 (by decide)
  have hx : kernel 18=(-1)*stepGamma2 1 := by decide
  rw [hx]
  exact K.mul_mem hz hh

#print axioms step2

theorem step3 (F : ℍ → ℂ) (k : ℤ) 
    (he : QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeTwo k F=0)
    (hz : F ∣[k] (-1:SL(2,ℤ))=F)
    (hk : ∀ j : Fin 24, j.val<20 → F ∣[k] kernel j=F) :
    F ∣[k] kernel 20=F := by
  let K := slashStabilizer k F
  have hknown (j : Fin 15) (hj : stageSize j=20) : F ∣[k] target j=F := by
    apply target_mem K hz j
    intro i hi
    apply hk i
    simpa only [hj] using hi
  have hB : (0:ℂ)=0 ∨ F ∣[k] stepB3=F := Or.inl rfl
  have hh : F ∣[k] stepGamma3 1=F := by
    refine SmallLevelFiniteHeckeStep.one_missing F k twoBranch stepB3 stepGamma3
      stepPerm3 1 (0:ℂ) ?_ hB (stepBranches3) ?_
    · simpa [twoBranch,Fin.sum_univ_succ,QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeTwo,add_assoc] using he
    · intro i hi
      fin_cases i
      · exact hknown 6 (by decide)
      · exact (hi rfl).elim
      · exact hknown 7 (by decide)
  exact hh

#print axioms step3

theorem step4 (F : ℍ → ℂ) (k : ℤ) (lam : ℂ) 
    (he : SmallLevelGoodHeckeFive.heckeFive k F=lam • F)
    (hz : F ∣[k] (-1:SL(2,ℤ))=F)
    (hk : ∀ j : Fin 24, j.val<22 → F ∣[k] kernel j=F) :
    F ∣[k] kernel 22=F := by
  let K := slashStabilizer k F
  have hknown (j : Fin 15) (hj : stageSize j=22) : F ∣[k] target j=F := by
    apply target_mem K hz j
    intro i hi
    apply hk i
    simpa only [hj] using hi
  have hB : lam=0 ∨ F ∣[k] stepB4=F := Or.inr (hknown 8 (by decide))
  have hh : F ∣[k] stepGamma4 1=F := by
    refine SmallLevelFiniteHeckeStep.one_missing F k fiveBranch stepB4 stepGamma4
      stepPerm4 1 lam ?_ hB (stepBranches4) ?_
    · simpa [fiveBranch,Fin.sum_univ_succ,SmallLevelGoodHeckeFive.heckeFive,add_assoc] using he
    · intro i hi
      fin_cases i
      · have hx : stepGamma4 0=(-1)*target 9 := by decide
        change F ∣[k] stepGamma4 0=F
        rw [hx]
        exact K.mul_mem hz (hknown 9 (by decide))
      · exact (hi rfl).elim
      · have hx : stepGamma4 2=(-1)*target 10 := by decide
        change F ∣[k] stepGamma4 2=F
        rw [hx]
        exact K.mul_mem hz (hknown 10 (by decide))
      · have hx : stepGamma4 3=(-1)*target 11 := by decide
        change F ∣[k] stepGamma4 3=F
        rw [hx]
        exact K.mul_mem hz (hknown 11 (by decide))
      · have hx : stepGamma4 4=(-1)*target 12 := by decide
        change F ∣[k] stepGamma4 4=F
        rw [hx]
        exact K.mul_mem hz (hknown 12 (by decide))
      · have hx : stepGamma4 5=(-1)*target 13 := by decide
        change F ∣[k] stepGamma4 5=F
        rw [hx]
        exact K.mul_mem hz (hknown 13 (by decide))
  have hx : kernel 22=(-1)*stepGamma4 1 := by decide
  rw [hx]
  exact K.mul_mem hz hh

#print axioms step4

end SmallLevelTwentyOneZero
end
end
