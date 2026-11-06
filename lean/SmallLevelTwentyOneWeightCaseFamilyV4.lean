module
public import SmallLevelTwentyOneAugmentedLaurentRowsV1
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightCase0
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne

def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((1*x^2*y*z))*w 41)

theorem row000_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 0)=row000 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row000,augmentedWordRows,augmentedRow000]
  <;> ring_nf <;> simp

def row001 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((1*y*z))*w 40)

theorem row001_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 1)=row001 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row001,augmentedWordRows,augmentedRow001]
  <;> ring_nf <;> simp

def row003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y*z)))*w 0+((1))*w 2)

theorem row003_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 3)=row003 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row003,augmentedWordRows,augmentedRow003]
  <;> ring_nf <;> simp

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((1*y)/(x^2*z)))*w 14)

theorem row004_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 4)=row004 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row004,augmentedWordRows,augmentedRow004]
  <;> ring_nf <;> simp

def row005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 4+(((1*x^2)/(y*z)))*w 21)

theorem row005_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 5)=row005 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row005,augmentedWordRows,augmentedRow005]
  <;> ring_nf <;> simp

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((1*y)/(z)))*w 28)

theorem row006_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 6)=row006 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row006,augmentedWordRows,augmentedRow006]
  <;> ring_nf <;> simp

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((1*z)/(x^2*y)))*w 30)

theorem row007_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 7)=row007 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row007,augmentedWordRows,augmentedRow007]
  <;> ring_nf <;> simp

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((1*x^2*y)/(z)))*w 35)

theorem row008_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 8)=row008 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row008,augmentedWordRows,augmentedRow008]
  <;> ring_nf <;> simp

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((1*z)/(y)))*w 36)

theorem row009_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 9)=row009 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row009,augmentedWordRows,augmentedRow009]
  <;> ring_nf <;> simp

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((1*y*z)/(x^2)))*w 38)

theorem row010_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 10)=row010 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row010,augmentedWordRows,augmentedRow010]
  <;> ring_nf <;> simp

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((1*x^2*z)/(y)))*w 39)

theorem row011_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 11)=row011 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row011,augmentedWordRows,augmentedRow011]
  <;> ring_nf <;> simp

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

theorem row038_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 38)=row038 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row038,augmentedWordRows,augmentedRow038]
  <;> ring_nf <;> simp

def row039 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 22+((-1*x^2))*w 41)

theorem row039_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 39)=row039 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row039,augmentedWordRows,augmentedRow039]
  <;> ring_nf <;> simp

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

theorem row040_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 40)=row040 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row040,augmentedWordRows,augmentedRow040]
  <;> ring_nf <;> simp

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

theorem row043_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 43)=row043 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row043,augmentedWordRows,augmentedRow043]
  <;> ring_nf <;> simp

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

theorem row047_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 47)=row047 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row047,augmentedWordRows,augmentedRow047]
  <;> ring_nf <;> simp

def row049 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((-1*x^2))*w 5+((1))*w 16)

theorem row049_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 49)=row049 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row049,augmentedWordRows,augmentedRow049]
  <;> ring_nf <;> simp

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

theorem row319_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 319)=row319 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row319,augmentedInfinityRows,augmentedInfinity000]
  <;> ring_nf <;> simp

def row387 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+(((1)/(z)))*w 14+((1))*w 16+((1))*w 30)

theorem row387_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 387)=row387 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row387,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1*x^2)/(z)))*w 7+((1))*w 18+(((1*x^2)/(z)))*w 21+((1))*w 32)

theorem row389_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 389)=row389 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row389,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 8+(((1)/(z)))*w 28+((1))*w 36)

theorem row397_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 397)=row397 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row397,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 6+(((1)/(z)))*w 14+((1))*w 34)

theorem row398_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 398)=row398 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row398,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y)))*w 0+(((1)/(y)))*w 6+((1))*w 8+(((1)/(y)))*w 12+((1))*w 14+(((1)/(y)))*w 18+((1))*w 20+(((1)/(y)))*w 24+((1))*w 26+(((1)/(y)))*w 30+((1))*w 32+((1))*w 38)

theorem row403_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 403)=row403 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row403,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row419 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((2))*w 6+((1))*w 8+((1))*w 10+((1))*w 12+((1))*w 14+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 28+((1))*w 30+((1))*w 32+((1))*w 34+((2))*w 36+((1))*w 38+((1))*w 40)

theorem row419_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 419)=row419 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row419,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row423 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((1))*w 6+((1))*w 10+((2))*w 12+((1))*w 14+((1))*w 16+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 26+((1))*w 28+((2))*w 30+((1))*w 32+((1))*w 36+((1))*w 38+((1))*w 40)

theorem row423_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 423)=row423 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row423,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

theorem row427_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 427)=row427 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row427,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

theorem row428_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 428)=row428 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row428,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

theorem row436_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 436)=row436 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row436,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def row438 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 5+(((-1*a)/(x)))*w 10+(((1)/(x^2)))*w 20+((1))*w 26)

theorem row438_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (-1) x y z a w (augmentedIndex 438)=row438 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row438,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def residual403 (x y z a : ℂ) : ℂ := (((-2)/(z))+(-1)+((1*y)/(z))+((1*x*a)/(z))+((1*x*y*a)/(z))+((1*x^2)/(z))+((1*x^2*y)/(z)))

theorem residual403_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((-1)/(y*z)))*row000 x y z a w+(((-1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((-1)/(y))+((1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((-1*x^2)/(z)))*row007 x y z a w+(((-2)/(y)))*row008 x y z a w+(((-1)/(z))+((1*y)/(z))+((-1*x^2)/(z))+((-1*x^2*y)/(z)))*row009 x y z a w+(((-1*x^2)/(y*z)))*row010 x y z a w+(((-1)/(z))+((1*y)/(z)))*row011 x y z a w+(((1*x^2)/(y*z))+((1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((-1)/(y))+(1))*row043 x y z a w+(((-1)/(y))+((-1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((2)/(y*z))+((-1)/(y))+((3)/(z)))*row319 x y z a w+((1))*row387 x y z a w+((-1))*row389 x y z a w+((-2))*row397 x y z a w+((-1))*row398 x y z a w+((1))*row403 x y z a w+((1))*row419 x y z a w+((-1))*row423 x y z a w+(((2)/(z))+(-1)+((1*x^2)/(z))+((1*x^2*y)/(z)))*row427 x y z a w+(((2*x^2)/(z)))*row428 x y z a w+(((1*x^2)/(y))+(1*x^2))*row436 x y z a w)=residual403 x y z a*w 28 := by
  dsimp only [residual403,row403,row319,row010,row038,row040,row000,row006,row043,row011,row047,row009,row427,row397,row428,row007,row008,row387,row423,row419,row398,row436,row004,row389]
  field_simp [hx,hy,hz]
  ring

def residual438 (x y z a : ℂ) : ℂ := (((1)/(x^2*z))+((-1*y)/(x^2*z))+((1*a)/(x*z))+((-1)/(z))+((1*a^2)/(z))+((1*x*a)/(z))+((1*x*y*a)/(z))+((1*x^2*y)/(z)))

theorem residual438_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((-1)/(x^2*y*z))+((-2*a)/(x*y*z)))*row000 x y z a w+(((-1*a)/(x*y*z)))*row001 x y z a w+(((-1*a)/(x)))*row003 x y z a w+((1)+((-1*x*a)/(y))+(-1*x^2))*row004 x y z a w+(((-1*a)/(x)))*row005 x y z a w+(((-2*a)/(x))+((1*a^2)/(y))+(1*x*a))*row006 x y z a w+(((1*y)/(z))+((-1*x*y*a)/(z)))*row007 x y z a w+(((1)/(x^2))+((-1*a)/(x*y))+((-1*a)/(x)))*row008 x y z a w+(((-3*y*a)/(x*z))+((1*y)/(z))+((-1*x*a)/(z))+((-1*x^2*y)/(z)))*row009 x y z a w+(((-1*x*a)/(y*z)))*row010 x y z a w+(((-1*y*a)/(x*z)))*row011 x y z a w+(((2*x*a)/(y*z))+((1*x*a)/(z)))*row038 x y z a w+(((-1*a)/(x)))*row039 x y z a w+(((-1)/(x^2))+((-1*a)/(x)))*row040 x y z a w+(((-1*a)/(x)))*row043 x y z a w+(((-2*a)/(x))+(1)+((-1*x*a)/(y))+(-1*x^2))*row047 x y z a w+(((1)/(x^2)))*row049 x y z a w+(((1)/(x^2*y*z))+((1)/(x^2*z))+((6*a)/(x*y*z))+((3*a)/(x*z))+((-2*a)/(x))+((1)/(z)))*row319 x y z a w+(((-1)/(x^2))+(1))*row387 x y z a w+(((-1*a)/(x)))*row389 x y z a w+(((-1*a)/(x))+(-1))*row397 x y z a w+(((-1*a)/(x))+(-1))*row398 x y z a w+(((1*a)/(x))+(1))*row419 x y z a w+((-1))*row423 x y z a w+(((1)/(x^2*z))+((-1*y)/(x^2*z))+((2*a)/(x*z))+((-1*a)/(x))+((3*y*a)/(x*z))+((1*x*a)/(z))+((1*x^2*y)/(z)))*row427 x y z a w+(((-1*y)/(z))+((1*x*a)/(z))+((1*x*y*a)/(z)))*row428 x y z a w+((-1)+((1*x*a)/(y))+(1*x^2))*row436 x y z a w+((1))*row438 x y z a w)=residual438 x y z a*w 28 := by
  dsimp only [residual438,row438,row040,row000,row319,row049,row419,row001,row003,row005,row038,row010,row039,row006,row009,row043,row011,row047,row427,row397,row398,row428,row007,row008,row423,row387,row436,row004,row389]
  field_simp [hx,hy,hz]
  ring

def weightPolynomial (x y z : ℂ) : ℂ := ((7)+(5*z)+(1*z^2)+(-2*y)+(-1*y*z)+(-1*y^2)+(-1*y^3)+(-4*x^2)+(-1*x^2*z)+(-3*x^2*y)+(1*x^2*y^2*z)+(-1*x^2*y^3))

theorem resultant_zero (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hL : residual403 x y z a=0) (hQ : residual438 x y z a=0) :
    weightPolynomial x y z=0 := by
  dsimp only [residual403] at hL
  dsimp only [residual438] at hQ
  have h : (((7)/(z^3))+((5)/(z^2))+((1)/(z))+((-2*y)/(z^3))+((-1*y)/(z^2))+((-1*y^2)/(z^3))+((-1*y^3)/(z^3))+((-4*x^2)/(z^3))+((-1*x^2)/(z^2))+((-3*x^2*y)/(z^3))+((1*x^2*y^2)/(z^2))+((-1*x^2*y^3)/(z^3)))=0 := by
    linear_combination (norm := skip)
      ((((1*x)/(z))+((1*x*y)/(z))))^2*hQ-((((1)/(z)))*((((1*x)/(z))+((1*x*y)/(z)))*a-(((-2)/(z))+(-1)+((1*y)/(z))+((1*x^2)/(z))+((1*x^2*y)/(z))))+(((1)/(x*z))+((1*x)/(z))+((1*x*y)/(z)))*(((1*x)/(z))+((1*x*y)/(z))))*hL
    field_simp [hx,hy,hz]
    ring
  dsimp only [weightPolynomial]
  field_simp [hx,hy,hz] at h ⊢
  linear_combination (norm := ring_nf) h

theorem leading_constraints (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (-1) (-1) (-1) x y z a w r=0) :
    residual403 x y z a=0 ∧ weightPolynomial x y z=0 := by
  have hr000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hr001 : row001 x y z a w=0 := by
    rw [← row001_link]; exact hker (augmentedIndex 1)
  have hr003 : row003 x y z a w=0 := by
    rw [← row003_link]; exact hker (augmentedIndex 3)
  have hr004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hr005 : row005 x y z a w=0 := by
    rw [← row005_link]; exact hker (augmentedIndex 5)
  have hr006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hr007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hr008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hr009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hr010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hr011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hr038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hr039 : row039 x y z a w=0 := by
    rw [← row039_link]; exact hker (augmentedIndex 39)
  have hr040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hr043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hr047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hr049 : row049 x y z a w=0 := by
    rw [← row049_link]; exact hker (augmentedIndex 49)
  have hr319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hr387 : row387 x y z a w=0 := by
    rw [← row387_link]; exact hker (augmentedIndex 387)
  have hr389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hr397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hr398 : row398 x y z a w=0 := by
    rw [← row398_link]; exact hker (augmentedIndex 398)
  have hr403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hr419 : row419 x y z a w=0 := by
    rw [← row419_link]; exact hker (augmentedIndex 419)
  have hr423 : row423 x y z a w=0 := by
    rw [← row423_link]; exact hker (augmentedIndex 423)
  have hr427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hr428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hr436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hr438 : row438 x y z a w=0 := by
    rw [← row438_link]; exact hker (augmentedIndex 438)
  have h403 := residual403_identity x y z a hx hy hz w
  simp only [hr000,hr001,hr003,hr004,hr005,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr039,hr040,hr043,hr047,hr049,hr319,hr387,hr389,hr397,hr398,hr403,hr419,hr423,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h403
  have h438 := residual438_identity x y z a hx hy hz w
  simp only [hr000,hr001,hr003,hr004,hr005,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr039,hr040,hr043,hr047,hr049,hr319,hr387,hr389,hr397,hr398,hr403,hr419,hr423,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h438
  exact ⟨h403.symm,resultant_zero x y z a hx hy hz h403.symm h438.symm⟩

#print axioms leading_constraints
end SmallLevelTwentyOneWeightCase0
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightCase1
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne

def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((1*x^2*y*z))*w 41)

theorem row000_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 0)=row000 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row000,augmentedWordRows,augmentedRow000]
  <;> ring_nf <;> simp

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((1*y)/(x^2*z)))*w 14)

theorem row004_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 4)=row004 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row004,augmentedWordRows,augmentedRow004]
  <;> ring_nf <;> simp

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((1*y)/(z)))*w 28)

theorem row006_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 6)=row006 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row006,augmentedWordRows,augmentedRow006]
  <;> ring_nf <;> simp

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((1*z)/(x^2*y)))*w 30)

theorem row007_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 7)=row007 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row007,augmentedWordRows,augmentedRow007]
  <;> ring_nf <;> simp

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((1*x^2*y)/(z)))*w 35)

theorem row008_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 8)=row008 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row008,augmentedWordRows,augmentedRow008]
  <;> ring_nf <;> simp

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((1*z)/(y)))*w 36)

theorem row009_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 9)=row009 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row009,augmentedWordRows,augmentedRow009]
  <;> ring_nf <;> simp

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((1*y*z)/(x^2)))*w 38)

theorem row010_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 10)=row010 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row010,augmentedWordRows,augmentedRow010]
  <;> ring_nf <;> simp

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((1*x^2*z)/(y)))*w 39)

theorem row011_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 11)=row011 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row011,augmentedWordRows,augmentedRow011]
  <;> ring_nf <;> simp

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

theorem row038_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 38)=row038 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row038,augmentedWordRows,augmentedRow038]
  <;> ring_nf <;> simp

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

theorem row040_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 40)=row040 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row040,augmentedWordRows,augmentedRow040]
  <;> ring_nf <;> simp

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

theorem row043_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 43)=row043 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row043,augmentedWordRows,augmentedRow043]
  <;> ring_nf <;> simp

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

theorem row047_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 47)=row047 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row047,augmentedWordRows,augmentedRow047]
  <;> ring_nf <;> simp

def row049 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((-1*x^2))*w 5+((1))*w 16)

theorem row049_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 49)=row049 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row049,augmentedWordRows,augmentedRow049]
  <;> ring_nf <;> simp

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

theorem row319_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 319)=row319 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row319,augmentedInfinityRows,augmentedInfinity000]
  <;> ring_nf <;> simp

def row387 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+(((1)/(z)))*w 14+((1))*w 16+((1))*w 30)

theorem row387_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 387)=row387 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row387,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row388 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 12+((1))*w 26+(((1)/(z)))*w 28)

theorem row388_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 388)=row388 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row388,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1*x^2)/(z)))*w 7+((1))*w 18+(((1*x^2)/(z)))*w 21+((1))*w 32)

theorem row389_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 389)=row389 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row389,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row390 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 10+(((1*x^2)/(z)))*w 21+((1))*w 24+(((1*x^2)/(z)))*w 35)

theorem row390_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 390)=row390 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row390,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 8+(((1)/(z)))*w 28+((1))*w 36)

theorem row397_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 397)=row397 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row397,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y)))*w 0+(((-1)/(y)))*w 6+((1))*w 8+(((-1)/(y)))*w 12+((1))*w 14+(((-1)/(y)))*w 18+((1))*w 20+(((-1)/(y)))*w 24+((1))*w 26+(((-1)/(y)))*w 30+((1))*w 32+((1))*w 38)

theorem row403_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 403)=row403 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row403,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

theorem row427_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 427)=row427 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row427,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

theorem row428_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 428)=row428 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row428,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

theorem row436_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 436)=row436 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row436,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def row438 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 5+(((-1*a)/(x)))*w 10+(((1)/(x^2)))*w 20+((1))*w 26)

theorem row438_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (-1) (1) x y z a w (augmentedIndex 438)=row438 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row438,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def residual403 (x y z a : ℂ) : ℂ := ((-1)+((1*y)/(z))+((1*x*a)/(z))+((1*x*y*a)/(z))+((1*x^2)/(z))+((1*x^2*y)/(z)))

theorem residual403_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((-1)/(y*z)))*row000 x y z a w+(((-1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((1)/(y))+((1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((1*x^2)/(z)))*row007 x y z a w+(((1)/(z))+((1*y)/(z))+((-1*x^2)/(z))+((-1*x^2*y)/(z)))*row009 x y z a w+(((-1*x^2)/(y*z)))*row010 x y z a w+(((1)/(z))+((1*y)/(z)))*row011 x y z a w+(((1*x^2)/(y*z))+((1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((1)/(y))+(1))*row043 x y z a w+(((1)/(y))+((-1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((2)/(y*z))+((1)/(y))+((3)/(z)))*row319 x y z a w+((-1))*row388 x y z a w+((-1))*row389 x y z a w+((-1))*row397 x y z a w+((1))*row403 x y z a w+((-1)+((1*x^2)/(z))+((1*x^2*y)/(z)))*row427 x y z a w+(((1*x^2)/(y))+(1*x^2))*row436 x y z a w)=residual403 x y z a*w 28 := by
  dsimp only [residual403,row403,row319,row010,row038,row040,row000,row006,row043,row011,row047,row009,row427,row397,row007,row388,row436,row004,row389]
  field_simp [hx,hy,hz]
  ring

def residual438 (x y z a : ℂ) : ℂ := (((1)/(x^2*z))+((-1*y)/(x^2*z))+((1*a)/(x*z))+((-1)/(z))+((1*a^2)/(z))+((1*x*a)/(z))+((1*x*y*a)/(z))+((1*x^2*y)/(z)))

theorem residual438_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((-1)/(x^2*y*z)))*row000 x y z a w+((1)+((-1*x*a)/(y))+(-1*x^2))*row004 x y z a w+(((-1*a)/(x))+((1*a^2)/(y))+(1*x*a))*row006 x y z a w+(((1*y)/(z)))*row007 x y z a w+(((1)/(x^2))+((-1*a)/(x*y)))*row008 x y z a w+(((-1*y*a)/(x*z))+((1*y)/(z))+((-1*x*a)/(z))+((-1*x^2*y)/(z)))*row009 x y z a w+(((-1*x*a)/(z)))*row038 x y z a w+(((-1)/(x^2)))*row040 x y z a w+(((-1*a)/(x))+(1)+((-1*x*a)/(y))+(-1*x^2))*row047 x y z a w+(((1)/(x^2)))*row049 x y z a w+(((1)/(x^2*y*z))+((1)/(x^2*z))+((-1*a)/(x*z))+((1)/(z)))*row319 x y z a w+(((-1)/(x^2)))*row387 x y z a w+((-1))*row388 x y z a w+(((1*a)/(x)))*row390 x y z a w+(((1)/(x^2*z))+((-1*y)/(x^2*z))+((1*a)/(x*z))+((1*y*a)/(x*z))+((1*x*a)/(z))+((1*x^2*y)/(z)))*row427 x y z a w+(((-1*y)/(z)))*row428 x y z a w+((-1)+((1*x*a)/(y))+(1*x^2))*row436 x y z a w+((1))*row438 x y z a w)=residual438 x y z a*w 28 := by
  dsimp only [residual438,row438,row040,row000,row319,row049,row387,row427,row436,row004,row006,row047,row009,row428,row007,row008,row388,row390,row038]
  field_simp [hx,hy,hz]
  ring

def weightPolynomial (x y z : ℂ) : ℂ := ((1)+(1*z)+(1*z^2)+(-1*y*z)+(-1*y^2)+(-1*y^3)+(-2*x^2)+(-1*x^2*z)+(-3*x^2*y)+(-2*x^2*y^2)+(1*x^2*y^2*z)+(-1*x^2*y^3))

theorem resultant_zero (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hL : residual403 x y z a=0) (hQ : residual438 x y z a=0) :
    weightPolynomial x y z=0 := by
  dsimp only [residual403] at hL
  dsimp only [residual438] at hQ
  have h : (((1)/(z^3))+((1)/(z^2))+((1)/(z))+((-1*y)/(z^2))+((-1*y^2)/(z^3))+((-1*y^3)/(z^3))+((-2*x^2)/(z^3))+((-1*x^2)/(z^2))+((-3*x^2*y)/(z^3))+((-2*x^2*y^2)/(z^3))+((1*x^2*y^2)/(z^2))+((-1*x^2*y^3)/(z^3)))=0 := by
    linear_combination (norm := skip)
      ((((1*x)/(z))+((1*x*y)/(z))))^2*hQ-((((1)/(z)))*((((1*x)/(z))+((1*x*y)/(z)))*a-((-1)+((1*y)/(z))+((1*x^2)/(z))+((1*x^2*y)/(z))))+(((1)/(x*z))+((1*x)/(z))+((1*x*y)/(z)))*(((1*x)/(z))+((1*x*y)/(z))))*hL
    field_simp [hx,hy,hz]
    ring
  dsimp only [weightPolynomial]
  field_simp [hx,hy,hz] at h ⊢
  linear_combination (norm := ring_nf) h

theorem leading_constraints (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (-1) (-1) (1) x y z a w r=0) :
    residual403 x y z a=0 ∧ weightPolynomial x y z=0 := by
  have hr000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hr004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hr006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hr007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hr008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hr009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hr010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hr011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hr038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hr040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hr043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hr047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hr049 : row049 x y z a w=0 := by
    rw [← row049_link]; exact hker (augmentedIndex 49)
  have hr319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hr387 : row387 x y z a w=0 := by
    rw [← row387_link]; exact hker (augmentedIndex 387)
  have hr388 : row388 x y z a w=0 := by
    rw [← row388_link]; exact hker (augmentedIndex 388)
  have hr389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hr390 : row390 x y z a w=0 := by
    rw [← row390_link]; exact hker (augmentedIndex 390)
  have hr397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hr403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hr427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hr428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hr436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hr438 : row438 x y z a w=0 := by
    rw [← row438_link]; exact hker (augmentedIndex 438)
  have h403 := residual403_identity x y z a hx hy hz w
  simp only [hr000,hr004,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr040,hr043,hr047,hr049,hr319,hr387,hr388,hr389,hr390,hr397,hr403,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h403
  have h438 := residual438_identity x y z a hx hy hz w
  simp only [hr000,hr004,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr040,hr043,hr047,hr049,hr319,hr387,hr388,hr389,hr390,hr397,hr403,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h438
  exact ⟨h403.symm,resultant_zero x y z a hx hy hz h403.symm h438.symm⟩

#print axioms leading_constraints
end SmallLevelTwentyOneWeightCase1
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightCase2
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne

def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((1*x^2*y*z))*w 41)

theorem row000_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 0)=row000 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row000,augmentedWordRows,augmentedRow000]
  <;> ring_nf <;> simp

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((1*y)/(x^2*z)))*w 14)

theorem row004_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 4)=row004 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row004,augmentedWordRows,augmentedRow004]
  <;> ring_nf <;> simp

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((1*y)/(z)))*w 28)

theorem row006_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 6)=row006 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row006,augmentedWordRows,augmentedRow006]
  <;> ring_nf <;> simp

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((1*z)/(x^2*y)))*w 30)

theorem row007_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 7)=row007 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row007,augmentedWordRows,augmentedRow007]
  <;> ring_nf <;> simp

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((1*x^2*y)/(z)))*w 35)

theorem row008_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 8)=row008 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row008,augmentedWordRows,augmentedRow008]
  <;> ring_nf <;> simp

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((1*z)/(y)))*w 36)

theorem row009_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 9)=row009 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row009,augmentedWordRows,augmentedRow009]
  <;> ring_nf <;> simp

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((1*y*z)/(x^2)))*w 38)

theorem row010_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 10)=row010 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row010,augmentedWordRows,augmentedRow010]
  <;> ring_nf <;> simp

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((1*x^2*z)/(y)))*w 39)

theorem row011_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 11)=row011 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row011,augmentedWordRows,augmentedRow011]
  <;> ring_nf <;> simp

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

theorem row038_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 38)=row038 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row038,augmentedWordRows,augmentedRow038]
  <;> ring_nf <;> simp

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

theorem row040_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 40)=row040 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row040,augmentedWordRows,augmentedRow040]
  <;> ring_nf <;> simp

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

theorem row043_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 43)=row043 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row043,augmentedWordRows,augmentedRow043]
  <;> ring_nf <;> simp

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

theorem row047_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 47)=row047 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row047,augmentedWordRows,augmentedRow047]
  <;> ring_nf <;> simp

def row049 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((-1*x^2))*w 5+((1))*w 16)

theorem row049_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 49)=row049 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row049,augmentedWordRows,augmentedRow049]
  <;> ring_nf <;> simp

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

theorem row319_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 319)=row319 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row319,augmentedInfinityRows,augmentedInfinity000]
  <;> ring_nf <;> simp

def row387 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+(((-1)/(z)))*w 14+((1))*w 16+((1))*w 30)

theorem row387_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 387)=row387 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row387,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row388 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 12+((1))*w 26+(((-1)/(z)))*w 28)

theorem row388_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 388)=row388 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row388,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1*x^2)/(z)))*w 7+((1))*w 18+(((-1*x^2)/(z)))*w 21+((1))*w 32)

theorem row389_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 389)=row389 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row389,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row390 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 10+(((-1*x^2)/(z)))*w 21+((1))*w 24+(((-1*x^2)/(z)))*w 35)

theorem row390_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 390)=row390 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row390,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 8+(((-1)/(z)))*w 28+((1))*w 36)

theorem row397_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 397)=row397 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row397,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y)))*w 0+(((1)/(y)))*w 6+((1))*w 8+(((1)/(y)))*w 12+((1))*w 14+(((1)/(y)))*w 18+((1))*w 20+(((1)/(y)))*w 24+((1))*w 26+(((1)/(y)))*w 30+((1))*w 32+((1))*w 38)

theorem row403_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 403)=row403 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row403,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

theorem row427_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 427)=row427 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row427,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

theorem row428_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 428)=row428 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row428,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

theorem row436_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 436)=row436 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row436,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def row438 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 5+(((-1*a)/(x)))*w 10+(((1)/(x^2)))*w 20+((1))*w 26)

theorem row438_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (-1) x y z a w (augmentedIndex 438)=row438 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row438,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def residual403 (x y z a : ℂ) : ℂ := ((-1)+((1*y)/(z))+((-1*x*a)/(z))+((1*x*y*a)/(z))+((-1*x^2)/(z))+((1*x^2*y)/(z)))

theorem residual403_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((-1)/(y*z)))*row000 x y z a w+(((1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((-1)/(y))+((-1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((-1*x^2)/(z)))*row007 x y z a w+(((-1)/(z))+((1*y)/(z))+((1*x^2)/(z))+((-1*x^2*y)/(z)))*row009 x y z a w+(((-1*x^2)/(y*z)))*row010 x y z a w+(((-1)/(z))+((1*y)/(z)))*row011 x y z a w+(((1*x^2)/(y*z))+((-1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((-1)/(y))+(1))*row043 x y z a w+(((-1)/(y))+((1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((2)/(y*z))+((-1)/(y))+((-3)/(z)))*row319 x y z a w+((-1))*row388 x y z a w+((-1))*row389 x y z a w+((-1))*row397 x y z a w+((1))*row403 x y z a w+((-1)+((-1*x^2)/(z))+((1*x^2*y)/(z)))*row427 x y z a w+(((-1*x^2)/(y))+(1*x^2))*row436 x y z a w)=residual403 x y z a*w 28 := by
  dsimp only [residual403,row403,row319,row010,row038,row040,row000,row006,row043,row011,row047,row009,row427,row397,row007,row388,row436,row004,row389]
  field_simp [hx,hy,hz]
  ring

def residual438 (x y z a : ℂ) : ℂ := (((-1)/(x^2*z))+((-1*y)/(x^2*z))+((-1*a)/(x*z))+((1)/(z))+((-1*a^2)/(z))+((-1*x*a)/(z))+((1*x*y*a)/(z))+((1*x^2*y)/(z)))

theorem residual438_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((-1)/(x^2*y*z)))*row000 x y z a w+((1)+((1*x*a)/(y))+(-1*x^2))*row004 x y z a w+(((-1*a)/(x))+((-1*a^2)/(y))+(1*x*a))*row006 x y z a w+(((1*y)/(z)))*row007 x y z a w+(((1)/(x^2))+((1*a)/(x*y)))*row008 x y z a w+(((-1*y*a)/(x*z))+((1*y)/(z))+((1*x*a)/(z))+((-1*x^2*y)/(z)))*row009 x y z a w+(((1*x*a)/(z)))*row038 x y z a w+(((-1)/(x^2)))*row040 x y z a w+(((-1*a)/(x))+(1)+((1*x*a)/(y))+(-1*x^2))*row047 x y z a w+(((1)/(x^2)))*row049 x y z a w+(((1)/(x^2*y*z))+((-1)/(x^2*z))+((1*a)/(x*z))+((-1)/(z)))*row319 x y z a w+(((-1)/(x^2)))*row387 x y z a w+((-1))*row388 x y z a w+(((1*a)/(x)))*row390 x y z a w+(((-1)/(x^2*z))+((-1*y)/(x^2*z))+((-1*a)/(x*z))+((1*y*a)/(x*z))+((-1*x*a)/(z))+((1*x^2*y)/(z)))*row427 x y z a w+(((-1*y)/(z)))*row428 x y z a w+((-1)+((-1*x*a)/(y))+(1*x^2))*row436 x y z a w+((1))*row438 x y z a w)=residual438 x y z a*w 28 := by
  dsimp only [residual438,row438,row040,row000,row319,row049,row387,row427,row436,row004,row006,row047,row009,row428,row007,row008,row388,row390,row038]
  field_simp [hx,hy,hz]
  ring

def weightPolynomial (x y z : ℂ) : ℂ := ((-1)+(1*z)+(-1*z^2)+(1*y*z)+(1*y^2)+(-1*y^3)+(2*x^2)+(-1*x^2*z)+(-3*x^2*y)+(2*x^2*y^2)+(1*x^2*y^2*z)+(-1*x^2*y^3))

theorem resultant_zero (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hL : residual403 x y z a=0) (hQ : residual438 x y z a=0) :
    weightPolynomial x y z=0 := by
  dsimp only [residual403] at hL
  dsimp only [residual438] at hQ
  have h : (((-1)/(z^3))+((1)/(z^2))+((-1)/(z))+((1*y)/(z^2))+((1*y^2)/(z^3))+((-1*y^3)/(z^3))+((2*x^2)/(z^3))+((-1*x^2)/(z^2))+((-3*x^2*y)/(z^3))+((2*x^2*y^2)/(z^3))+((1*x^2*y^2)/(z^2))+((-1*x^2*y^3)/(z^3)))=0 := by
    linear_combination (norm := skip)
      ((((-1*x)/(z))+((1*x*y)/(z))))^2*hQ-((((-1)/(z)))*((((-1*x)/(z))+((1*x*y)/(z)))*a-((-1)+((1*y)/(z))+((-1*x^2)/(z))+((1*x^2*y)/(z))))+(((-1)/(x*z))+((-1*x)/(z))+((1*x*y)/(z)))*(((-1*x)/(z))+((1*x*y)/(z))))*hL
    field_simp [hx,hy,hz]
    ring
  dsimp only [weightPolynomial]
  field_simp [hx,hy,hz] at h ⊢
  linear_combination (norm := ring_nf) h

theorem leading_constraints (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (-1) (1) (-1) x y z a w r=0) :
    residual403 x y z a=0 ∧ weightPolynomial x y z=0 := by
  have hr000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hr004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hr006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hr007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hr008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hr009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hr010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hr011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hr038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hr040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hr043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hr047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hr049 : row049 x y z a w=0 := by
    rw [← row049_link]; exact hker (augmentedIndex 49)
  have hr319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hr387 : row387 x y z a w=0 := by
    rw [← row387_link]; exact hker (augmentedIndex 387)
  have hr388 : row388 x y z a w=0 := by
    rw [← row388_link]; exact hker (augmentedIndex 388)
  have hr389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hr390 : row390 x y z a w=0 := by
    rw [← row390_link]; exact hker (augmentedIndex 390)
  have hr397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hr403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hr427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hr428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hr436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hr438 : row438 x y z a w=0 := by
    rw [← row438_link]; exact hker (augmentedIndex 438)
  have h403 := residual403_identity x y z a hx hy hz w
  simp only [hr000,hr004,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr040,hr043,hr047,hr049,hr319,hr387,hr388,hr389,hr390,hr397,hr403,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h403
  have h438 := residual438_identity x y z a hx hy hz w
  simp only [hr000,hr004,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr040,hr043,hr047,hr049,hr319,hr387,hr388,hr389,hr390,hr397,hr403,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h438
  exact ⟨h403.symm,resultant_zero x y z a hx hy hz h403.symm h438.symm⟩

#print axioms leading_constraints
end SmallLevelTwentyOneWeightCase2
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightCase3
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne

def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((1*x^2*y*z))*w 41)

theorem row000_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 0)=row000 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row000,augmentedWordRows,augmentedRow000]
  <;> ring_nf <;> simp

def row001 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((1*y*z))*w 40)

theorem row001_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 1)=row001 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row001,augmentedWordRows,augmentedRow001]
  <;> ring_nf <;> simp

def row003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y*z)))*w 0+((1))*w 2)

theorem row003_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 3)=row003 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row003,augmentedWordRows,augmentedRow003]
  <;> ring_nf <;> simp

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((1*y)/(x^2*z)))*w 14)

theorem row004_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 4)=row004 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row004,augmentedWordRows,augmentedRow004]
  <;> ring_nf <;> simp

def row005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 4+(((1*x^2)/(y*z)))*w 21)

theorem row005_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 5)=row005 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row005,augmentedWordRows,augmentedRow005]
  <;> ring_nf <;> simp

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((1*y)/(z)))*w 28)

theorem row006_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 6)=row006 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row006,augmentedWordRows,augmentedRow006]
  <;> ring_nf <;> simp

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((1*z)/(x^2*y)))*w 30)

theorem row007_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 7)=row007 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row007,augmentedWordRows,augmentedRow007]
  <;> ring_nf <;> simp

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((1*x^2*y)/(z)))*w 35)

theorem row008_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 8)=row008 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row008,augmentedWordRows,augmentedRow008]
  <;> ring_nf <;> simp

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((1*z)/(y)))*w 36)

theorem row009_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 9)=row009 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row009,augmentedWordRows,augmentedRow009]
  <;> ring_nf <;> simp

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((1*y*z)/(x^2)))*w 38)

theorem row010_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 10)=row010 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row010,augmentedWordRows,augmentedRow010]
  <;> ring_nf <;> simp

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((1*x^2*z)/(y)))*w 39)

theorem row011_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 11)=row011 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row011,augmentedWordRows,augmentedRow011]
  <;> ring_nf <;> simp

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

theorem row038_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 38)=row038 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row038,augmentedWordRows,augmentedRow038]
  <;> ring_nf <;> simp

def row039 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 22+((-1*x^2))*w 41)

theorem row039_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 39)=row039 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row039,augmentedWordRows,augmentedRow039]
  <;> ring_nf <;> simp

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

theorem row040_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 40)=row040 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row040,augmentedWordRows,augmentedRow040]
  <;> ring_nf <;> simp

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

theorem row043_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 43)=row043 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row043,augmentedWordRows,augmentedRow043]
  <;> ring_nf <;> simp

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

theorem row047_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 47)=row047 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row047,augmentedWordRows,augmentedRow047]
  <;> ring_nf <;> simp

def row049 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((-1*x^2))*w 5+((1))*w 16)

theorem row049_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 49)=row049 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row049,augmentedWordRows,augmentedRow049]
  <;> ring_nf <;> simp

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

theorem row319_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 319)=row319 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row319,augmentedInfinityRows,augmentedInfinity000]
  <;> ring_nf <;> simp

def row387 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+(((-1)/(z)))*w 14+((1))*w 16+((1))*w 30)

theorem row387_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 387)=row387 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row387,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1*x^2)/(z)))*w 7+((1))*w 18+(((-1*x^2)/(z)))*w 21+((1))*w 32)

theorem row389_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 389)=row389 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row389,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 8+(((-1)/(z)))*w 28+((1))*w 36)

theorem row397_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 397)=row397 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row397,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 6+(((-1)/(z)))*w 14+((1))*w 34)

theorem row398_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 398)=row398 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row398,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y)))*w 0+(((-1)/(y)))*w 6+((1))*w 8+(((-1)/(y)))*w 12+((1))*w 14+(((-1)/(y)))*w 18+((1))*w 20+(((-1)/(y)))*w 24+((1))*w 26+(((-1)/(y)))*w 30+((1))*w 32+((1))*w 38)

theorem row403_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 403)=row403 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row403,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row419 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((2))*w 6+((1))*w 8+((1))*w 10+((1))*w 12+((1))*w 14+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 28+((1))*w 30+((1))*w 32+((1))*w 34+((2))*w 36+((1))*w 38+((1))*w 40)

theorem row419_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 419)=row419 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row419,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row423 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((1))*w 6+((1))*w 10+((2))*w 12+((1))*w 14+((1))*w 16+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 26+((1))*w 28+((2))*w 30+((1))*w 32+((1))*w 36+((1))*w 38+((1))*w 40)

theorem row423_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 423)=row423 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row423,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

theorem row427_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 427)=row427 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row427,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

theorem row428_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 428)=row428 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row428,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

theorem row436_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 436)=row436 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row436,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def row438 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 5+(((-1*a)/(x)))*w 10+(((1)/(x^2)))*w 20+((1))*w 26)

theorem row438_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (-1) (1) (1) x y z a w (augmentedIndex 438)=row438 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row438,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def residual403 (x y z a : ℂ) : ℂ := (((2)/(z))+(-1)+((1*y)/(z))+((-1*x*a)/(z))+((1*x*y*a)/(z))+((-1*x^2)/(z))+((1*x^2*y)/(z)))

theorem residual403_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((-1)/(y*z)))*row000 x y z a w+(((1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((1)/(y))+((-1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((1*x^2)/(z)))*row007 x y z a w+(((2)/(y)))*row008 x y z a w+(((1)/(z))+((1*y)/(z))+((1*x^2)/(z))+((-1*x^2*y)/(z)))*row009 x y z a w+(((-1*x^2)/(y*z)))*row010 x y z a w+(((1)/(z))+((1*y)/(z)))*row011 x y z a w+(((1*x^2)/(y*z))+((-1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((1)/(y))+(1))*row043 x y z a w+(((1)/(y))+((1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((2)/(y*z))+((1)/(y))+((-3)/(z)))*row319 x y z a w+((1))*row387 x y z a w+((-1))*row389 x y z a w+((-2))*row397 x y z a w+((-1))*row398 x y z a w+((1))*row403 x y z a w+((1))*row419 x y z a w+((-1))*row423 x y z a w+(((-2)/(z))+(-1)+((-1*x^2)/(z))+((1*x^2*y)/(z)))*row427 x y z a w+(((-2*x^2)/(z)))*row428 x y z a w+(((-1*x^2)/(y))+(1*x^2))*row436 x y z a w)=residual403 x y z a*w 28 := by
  dsimp only [residual403,row403,row319,row010,row038,row040,row000,row006,row043,row011,row047,row009,row427,row397,row428,row007,row008,row387,row423,row419,row398,row436,row004,row389]
  field_simp [hx,hy,hz]
  ring

def residual438 (x y z a : ℂ) : ℂ := (((-1)/(x^2*z))+((-1*y)/(x^2*z))+((-1*a)/(x*z))+((1)/(z))+((-1*a^2)/(z))+((-1*x*a)/(z))+((1*x*y*a)/(z))+((1*x^2*y)/(z)))

theorem residual438_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((-1)/(x^2*y*z))+((-2*a)/(x*y*z)))*row000 x y z a w+(((-1*a)/(x*y*z)))*row001 x y z a w+(((-1*a)/(x)))*row003 x y z a w+((1)+((1*x*a)/(y))+(-1*x^2))*row004 x y z a w+(((-1*a)/(x)))*row005 x y z a w+(((-2*a)/(x))+((-1*a^2)/(y))+(1*x*a))*row006 x y z a w+(((1*y)/(z))+((-1*x*y*a)/(z)))*row007 x y z a w+(((1)/(x^2))+((1*a)/(x*y))+((-1*a)/(x)))*row008 x y z a w+(((-3*y*a)/(x*z))+((1*y)/(z))+((1*x*a)/(z))+((-1*x^2*y)/(z)))*row009 x y z a w+(((-1*x*a)/(y*z)))*row010 x y z a w+(((-1*y*a)/(x*z)))*row011 x y z a w+(((2*x*a)/(y*z))+((-1*x*a)/(z)))*row038 x y z a w+(((-1*a)/(x)))*row039 x y z a w+(((-1)/(x^2))+((-1*a)/(x)))*row040 x y z a w+(((-1*a)/(x)))*row043 x y z a w+(((-2*a)/(x))+(1)+((1*x*a)/(y))+(-1*x^2))*row047 x y z a w+(((1)/(x^2)))*row049 x y z a w+(((1)/(x^2*y*z))+((-1)/(x^2*z))+((6*a)/(x*y*z))+((-3*a)/(x*z))+((-2*a)/(x))+((-1)/(z)))*row319 x y z a w+(((-1)/(x^2))+(1))*row387 x y z a w+(((-1*a)/(x)))*row389 x y z a w+(((-1*a)/(x))+(-1))*row397 x y z a w+(((-1*a)/(x))+(-1))*row398 x y z a w+(((1*a)/(x))+(1))*row419 x y z a w+((-1))*row423 x y z a w+(((-1)/(x^2*z))+((-1*y)/(x^2*z))+((-2*a)/(x*z))+((-1*a)/(x))+((3*y*a)/(x*z))+((-1*x*a)/(z))+((1*x^2*y)/(z)))*row427 x y z a w+(((-1*y)/(z))+((-1*x*a)/(z))+((1*x*y*a)/(z)))*row428 x y z a w+((-1)+((-1*x*a)/(y))+(1*x^2))*row436 x y z a w+((1))*row438 x y z a w)=residual438 x y z a*w 28 := by
  dsimp only [residual438,row438,row040,row000,row319,row049,row419,row001,row003,row005,row038,row010,row039,row006,row009,row043,row011,row047,row427,row397,row398,row428,row007,row008,row423,row387,row436,row004,row389]
  field_simp [hx,hy,hz]
  ring

def weightPolynomial (x y z : ℂ) : ℂ := ((-7)+(5*z)+(-1*z^2)+(-2*y)+(1*y*z)+(1*y^2)+(-1*y^3)+(4*x^2)+(-1*x^2*z)+(-3*x^2*y)+(1*x^2*y^2*z)+(-1*x^2*y^3))

theorem resultant_zero (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hL : residual403 x y z a=0) (hQ : residual438 x y z a=0) :
    weightPolynomial x y z=0 := by
  dsimp only [residual403] at hL
  dsimp only [residual438] at hQ
  have h : (((-7)/(z^3))+((5)/(z^2))+((-1)/(z))+((-2*y)/(z^3))+((1*y)/(z^2))+((1*y^2)/(z^3))+((-1*y^3)/(z^3))+((4*x^2)/(z^3))+((-1*x^2)/(z^2))+((-3*x^2*y)/(z^3))+((1*x^2*y^2)/(z^2))+((-1*x^2*y^3)/(z^3)))=0 := by
    linear_combination (norm := skip)
      ((((-1*x)/(z))+((1*x*y)/(z))))^2*hQ-((((-1)/(z)))*((((-1*x)/(z))+((1*x*y)/(z)))*a-(((2)/(z))+(-1)+((1*y)/(z))+((-1*x^2)/(z))+((1*x^2*y)/(z))))+(((-1)/(x*z))+((-1*x)/(z))+((1*x*y)/(z)))*(((-1*x)/(z))+((1*x*y)/(z))))*hL
    field_simp [hx,hy,hz]
    ring
  dsimp only [weightPolynomial]
  field_simp [hx,hy,hz] at h ⊢
  linear_combination (norm := ring_nf) h

theorem leading_constraints (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (-1) (1) (1) x y z a w r=0) :
    residual403 x y z a=0 ∧ weightPolynomial x y z=0 := by
  have hr000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hr001 : row001 x y z a w=0 := by
    rw [← row001_link]; exact hker (augmentedIndex 1)
  have hr003 : row003 x y z a w=0 := by
    rw [← row003_link]; exact hker (augmentedIndex 3)
  have hr004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hr005 : row005 x y z a w=0 := by
    rw [← row005_link]; exact hker (augmentedIndex 5)
  have hr006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hr007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hr008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hr009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hr010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hr011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hr038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hr039 : row039 x y z a w=0 := by
    rw [← row039_link]; exact hker (augmentedIndex 39)
  have hr040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hr043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hr047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hr049 : row049 x y z a w=0 := by
    rw [← row049_link]; exact hker (augmentedIndex 49)
  have hr319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hr387 : row387 x y z a w=0 := by
    rw [← row387_link]; exact hker (augmentedIndex 387)
  have hr389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hr397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hr398 : row398 x y z a w=0 := by
    rw [← row398_link]; exact hker (augmentedIndex 398)
  have hr403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hr419 : row419 x y z a w=0 := by
    rw [← row419_link]; exact hker (augmentedIndex 419)
  have hr423 : row423 x y z a w=0 := by
    rw [← row423_link]; exact hker (augmentedIndex 423)
  have hr427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hr428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hr436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hr438 : row438 x y z a w=0 := by
    rw [← row438_link]; exact hker (augmentedIndex 438)
  have h403 := residual403_identity x y z a hx hy hz w
  simp only [hr000,hr001,hr003,hr004,hr005,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr039,hr040,hr043,hr047,hr049,hr319,hr387,hr389,hr397,hr398,hr403,hr419,hr423,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h403
  have h438 := residual438_identity x y z a hx hy hz w
  simp only [hr000,hr001,hr003,hr004,hr005,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr039,hr040,hr043,hr047,hr049,hr319,hr387,hr389,hr397,hr398,hr403,hr419,hr423,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h438
  exact ⟨h403.symm,resultant_zero x y z a hx hy hz h403.symm h438.symm⟩

#print axioms leading_constraints
end SmallLevelTwentyOneWeightCase3
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightCase4
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne

def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((-1*x^2*y*z))*w 41)

theorem row000_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 0)=row000 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row000,augmentedWordRows,augmentedRow000]
  <;> ring_nf <;> simp

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*y)/(x^2*z)))*w 14)

theorem row004_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 4)=row004 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row004,augmentedWordRows,augmentedRow004]
  <;> ring_nf <;> simp

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((-1*y)/(z)))*w 28)

theorem row006_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 6)=row006 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row006,augmentedWordRows,augmentedRow006]
  <;> ring_nf <;> simp

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((-1*z)/(x^2*y)))*w 30)

theorem row007_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 7)=row007 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row007,augmentedWordRows,augmentedRow007]
  <;> ring_nf <;> simp

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((-1*x^2*y)/(z)))*w 35)

theorem row008_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 8)=row008 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row008,augmentedWordRows,augmentedRow008]
  <;> ring_nf <;> simp

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((-1*z)/(y)))*w 36)

theorem row009_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 9)=row009 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row009,augmentedWordRows,augmentedRow009]
  <;> ring_nf <;> simp

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((-1*y*z)/(x^2)))*w 38)

theorem row010_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 10)=row010 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row010,augmentedWordRows,augmentedRow010]
  <;> ring_nf <;> simp

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((-1*x^2*z)/(y)))*w 39)

theorem row011_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 11)=row011 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row011,augmentedWordRows,augmentedRow011]
  <;> ring_nf <;> simp

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

theorem row038_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 38)=row038 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row038,augmentedWordRows,augmentedRow038]
  <;> ring_nf <;> simp

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

theorem row040_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 40)=row040 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row040,augmentedWordRows,augmentedRow040]
  <;> ring_nf <;> simp

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

theorem row043_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 43)=row043 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row043,augmentedWordRows,augmentedRow043]
  <;> ring_nf <;> simp

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

theorem row047_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 47)=row047 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row047,augmentedWordRows,augmentedRow047]
  <;> ring_nf <;> simp

def row049 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((-1*x^2))*w 5+((1))*w 16)

theorem row049_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 49)=row049 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row049,augmentedWordRows,augmentedRow049]
  <;> ring_nf <;> simp

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

theorem row319_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 319)=row319 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row319,augmentedInfinityRows,augmentedInfinity000]
  <;> ring_nf <;> simp

def row387 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+(((-1)/(z)))*w 14+((1))*w 16+((1))*w 30)

theorem row387_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 387)=row387 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row387,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row388 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 12+((1))*w 26+(((-1)/(z)))*w 28)

theorem row388_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 388)=row388 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row388,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1*x^2)/(z)))*w 7+((1))*w 18+(((-1*x^2)/(z)))*w 21+((1))*w 32)

theorem row389_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 389)=row389 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row389,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row390 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 10+(((-1*x^2)/(z)))*w 21+((1))*w 24+(((-1*x^2)/(z)))*w 35)

theorem row390_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 390)=row390 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row390,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 8+(((-1)/(z)))*w 28+((1))*w 36)

theorem row397_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 397)=row397 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row397,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y)))*w 0+(((-1)/(y)))*w 6+((1))*w 8+(((-1)/(y)))*w 12+((1))*w 14+(((-1)/(y)))*w 18+((1))*w 20+(((-1)/(y)))*w 24+((1))*w 26+(((-1)/(y)))*w 30+((1))*w 32+((1))*w 38)

theorem row403_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 403)=row403 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row403,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

theorem row427_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 427)=row427 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row427,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

theorem row428_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 428)=row428 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row428,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

theorem row436_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 436)=row436 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row436,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def row438 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 5+(((-1*a)/(x)))*w 10+(((1)/(x^2)))*w 20+((1))*w 26)

theorem row438_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (-1) x y z a w (augmentedIndex 438)=row438 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row438,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def residual403 (x y z a : ℂ) : ℂ := ((-1)+((-1*y)/(z))+((-1*x*a)/(z))+((-1*x*y*a)/(z))+((-1*x^2)/(z))+((-1*x^2*y)/(z)))

theorem residual403_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((1)/(y*z)))*row000 x y z a w+(((-1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((1)/(y))+((1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((-1*x^2)/(z)))*row007 x y z a w+(((-1)/(z))+((-1*y)/(z))+((1*x^2)/(z))+((1*x^2*y)/(z)))*row009 x y z a w+(((1*x^2)/(y*z)))*row010 x y z a w+(((-1)/(z))+((-1*y)/(z)))*row011 x y z a w+(((-1*x^2)/(y*z))+((-1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((1)/(y))+(1))*row043 x y z a w+(((1)/(y))+((-1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((-2)/(y*z))+((1)/(y))+((-3)/(z)))*row319 x y z a w+((-1))*row388 x y z a w+((-1))*row389 x y z a w+((-1))*row397 x y z a w+((1))*row403 x y z a w+((-1)+((-1*x^2)/(z))+((-1*x^2*y)/(z)))*row427 x y z a w+(((1*x^2)/(y))+(1*x^2))*row436 x y z a w)=residual403 x y z a*w 28 := by
  dsimp only [residual403,row403,row319,row010,row038,row040,row000,row006,row043,row011,row047,row009,row427,row397,row007,row388,row436,row004,row389]
  field_simp [hx,hy,hz]
  ring

def residual438 (x y z a : ℂ) : ℂ := (((-1)/(x^2*z))+((1*y)/(x^2*z))+((-1*a)/(x*z))+((1)/(z))+((-1*a^2)/(z))+((-1*x*a)/(z))+((-1*x*y*a)/(z))+((-1*x^2*y)/(z)))

theorem residual438_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((1)/(x^2*y*z)))*row000 x y z a w+((1)+((-1*x*a)/(y))+(-1*x^2))*row004 x y z a w+(((-1*a)/(x))+((1*a^2)/(y))+(1*x*a))*row006 x y z a w+(((-1*y)/(z)))*row007 x y z a w+(((1)/(x^2))+((-1*a)/(x*y)))*row008 x y z a w+(((1*y*a)/(x*z))+((-1*y)/(z))+((1*x*a)/(z))+((1*x^2*y)/(z)))*row009 x y z a w+(((1*x*a)/(z)))*row038 x y z a w+(((-1)/(x^2)))*row040 x y z a w+(((-1*a)/(x))+(1)+((-1*x*a)/(y))+(-1*x^2))*row047 x y z a w+(((1)/(x^2)))*row049 x y z a w+(((-1)/(x^2*y*z))+((-1)/(x^2*z))+((1*a)/(x*z))+((-1)/(z)))*row319 x y z a w+(((-1)/(x^2)))*row387 x y z a w+((-1))*row388 x y z a w+(((1*a)/(x)))*row390 x y z a w+(((-1)/(x^2*z))+((1*y)/(x^2*z))+((-1*a)/(x*z))+((-1*y*a)/(x*z))+((-1*x*a)/(z))+((-1*x^2*y)/(z)))*row427 x y z a w+(((1*y)/(z)))*row428 x y z a w+((-1)+((1*x*a)/(y))+(1*x^2))*row436 x y z a w+((1))*row438 x y z a w)=residual438 x y z a*w 28 := by
  dsimp only [residual438,row438,row040,row000,row319,row049,row387,row427,row436,row004,row006,row047,row009,row428,row007,row008,row388,row390,row038]
  field_simp [hx,hy,hz]
  ring

def weightPolynomial (x y z : ℂ) : ℂ := ((-1)+(1*z)+(-1*z^2)+(-1*y*z)+(1*y^2)+(1*y^3)+(2*x^2)+(-1*x^2*z)+(3*x^2*y)+(2*x^2*y^2)+(1*x^2*y^2*z)+(1*x^2*y^3))

theorem resultant_zero (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hL : residual403 x y z a=0) (hQ : residual438 x y z a=0) :
    weightPolynomial x y z=0 := by
  dsimp only [residual403] at hL
  dsimp only [residual438] at hQ
  have h : (((-1)/(z^3))+((1)/(z^2))+((-1)/(z))+((-1*y)/(z^2))+((1*y^2)/(z^3))+((1*y^3)/(z^3))+((2*x^2)/(z^3))+((-1*x^2)/(z^2))+((3*x^2*y)/(z^3))+((2*x^2*y^2)/(z^3))+((1*x^2*y^2)/(z^2))+((1*x^2*y^3)/(z^3)))=0 := by
    linear_combination (norm := skip)
      ((((-1*x)/(z))+((-1*x*y)/(z))))^2*hQ-((((-1)/(z)))*((((-1*x)/(z))+((-1*x*y)/(z)))*a-((-1)+((-1*y)/(z))+((-1*x^2)/(z))+((-1*x^2*y)/(z))))+(((-1)/(x*z))+((-1*x)/(z))+((-1*x*y)/(z)))*(((-1*x)/(z))+((-1*x*y)/(z))))*hL
    field_simp [hx,hy,hz]
    ring
  dsimp only [weightPolynomial]
  field_simp [hx,hy,hz] at h ⊢
  linear_combination (norm := ring_nf) h

theorem leading_constraints (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (1) (-1) (-1) x y z a w r=0) :
    residual403 x y z a=0 ∧ weightPolynomial x y z=0 := by
  have hr000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hr004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hr006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hr007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hr008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hr009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hr010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hr011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hr038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hr040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hr043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hr047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hr049 : row049 x y z a w=0 := by
    rw [← row049_link]; exact hker (augmentedIndex 49)
  have hr319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hr387 : row387 x y z a w=0 := by
    rw [← row387_link]; exact hker (augmentedIndex 387)
  have hr388 : row388 x y z a w=0 := by
    rw [← row388_link]; exact hker (augmentedIndex 388)
  have hr389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hr390 : row390 x y z a w=0 := by
    rw [← row390_link]; exact hker (augmentedIndex 390)
  have hr397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hr403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hr427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hr428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hr436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hr438 : row438 x y z a w=0 := by
    rw [← row438_link]; exact hker (augmentedIndex 438)
  have h403 := residual403_identity x y z a hx hy hz w
  simp only [hr000,hr004,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr040,hr043,hr047,hr049,hr319,hr387,hr388,hr389,hr390,hr397,hr403,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h403
  have h438 := residual438_identity x y z a hx hy hz w
  simp only [hr000,hr004,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr040,hr043,hr047,hr049,hr319,hr387,hr388,hr389,hr390,hr397,hr403,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h438
  exact ⟨h403.symm,resultant_zero x y z a hx hy hz h403.symm h438.symm⟩

#print axioms leading_constraints
end SmallLevelTwentyOneWeightCase4
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightCase5
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne

def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((-1*x^2*y*z))*w 41)

theorem row000_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 0)=row000 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row000,augmentedWordRows,augmentedRow000]
  <;> ring_nf <;> simp

def row001 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((-1*y*z))*w 40)

theorem row001_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 1)=row001 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row001,augmentedWordRows,augmentedRow001]
  <;> ring_nf <;> simp

def row003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y*z)))*w 0+((1))*w 2)

theorem row003_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 3)=row003 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row003,augmentedWordRows,augmentedRow003]
  <;> ring_nf <;> simp

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*y)/(x^2*z)))*w 14)

theorem row004_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 4)=row004 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row004,augmentedWordRows,augmentedRow004]
  <;> ring_nf <;> simp

def row005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 4+(((-1*x^2)/(y*z)))*w 21)

theorem row005_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 5)=row005 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row005,augmentedWordRows,augmentedRow005]
  <;> ring_nf <;> simp

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((-1*y)/(z)))*w 28)

theorem row006_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 6)=row006 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row006,augmentedWordRows,augmentedRow006]
  <;> ring_nf <;> simp

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((-1*z)/(x^2*y)))*w 30)

theorem row007_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 7)=row007 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row007,augmentedWordRows,augmentedRow007]
  <;> ring_nf <;> simp

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((-1*x^2*y)/(z)))*w 35)

theorem row008_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 8)=row008 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row008,augmentedWordRows,augmentedRow008]
  <;> ring_nf <;> simp

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((-1*z)/(y)))*w 36)

theorem row009_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 9)=row009 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row009,augmentedWordRows,augmentedRow009]
  <;> ring_nf <;> simp

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((-1*y*z)/(x^2)))*w 38)

theorem row010_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 10)=row010 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row010,augmentedWordRows,augmentedRow010]
  <;> ring_nf <;> simp

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((-1*x^2*z)/(y)))*w 39)

theorem row011_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 11)=row011 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row011,augmentedWordRows,augmentedRow011]
  <;> ring_nf <;> simp

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

theorem row038_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 38)=row038 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row038,augmentedWordRows,augmentedRow038]
  <;> ring_nf <;> simp

def row039 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 22+((-1*x^2))*w 41)

theorem row039_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 39)=row039 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row039,augmentedWordRows,augmentedRow039]
  <;> ring_nf <;> simp

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

theorem row040_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 40)=row040 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row040,augmentedWordRows,augmentedRow040]
  <;> ring_nf <;> simp

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

theorem row043_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 43)=row043 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row043,augmentedWordRows,augmentedRow043]
  <;> ring_nf <;> simp

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

theorem row047_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 47)=row047 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row047,augmentedWordRows,augmentedRow047]
  <;> ring_nf <;> simp

def row049 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((-1*x^2))*w 5+((1))*w 16)

theorem row049_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 49)=row049 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row049,augmentedWordRows,augmentedRow049]
  <;> ring_nf <;> simp

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

theorem row319_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 319)=row319 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row319,augmentedInfinityRows,augmentedInfinity000]
  <;> ring_nf <;> simp

def row387 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+(((-1)/(z)))*w 14+((1))*w 16+((1))*w 30)

theorem row387_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 387)=row387 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row387,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1*x^2)/(z)))*w 7+((1))*w 18+(((-1*x^2)/(z)))*w 21+((1))*w 32)

theorem row389_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 389)=row389 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row389,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 8+(((-1)/(z)))*w 28+((1))*w 36)

theorem row397_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 397)=row397 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row397,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 6+(((-1)/(z)))*w 14+((1))*w 34)

theorem row398_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 398)=row398 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row398,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y)))*w 0+(((1)/(y)))*w 6+((1))*w 8+(((1)/(y)))*w 12+((1))*w 14+(((1)/(y)))*w 18+((1))*w 20+(((1)/(y)))*w 24+((1))*w 26+(((1)/(y)))*w 30+((1))*w 32+((1))*w 38)

theorem row403_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 403)=row403 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row403,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row419 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((2))*w 6+((1))*w 8+((1))*w 10+((1))*w 12+((1))*w 14+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 28+((1))*w 30+((1))*w 32+((1))*w 34+((2))*w 36+((1))*w 38+((1))*w 40)

theorem row419_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 419)=row419 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row419,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row423 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((1))*w 6+((1))*w 10+((2))*w 12+((1))*w 14+((1))*w 16+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 26+((1))*w 28+((2))*w 30+((1))*w 32+((1))*w 36+((1))*w 38+((1))*w 40)

theorem row423_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 423)=row423 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row423,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

theorem row427_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 427)=row427 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row427,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

theorem row428_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 428)=row428 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row428,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

theorem row436_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 436)=row436 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row436,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def row438 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 5+(((-1*a)/(x)))*w 10+(((1)/(x^2)))*w 20+((1))*w 26)

theorem row438_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (-1) (1) x y z a w (augmentedIndex 438)=row438 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row438,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def residual403 (x y z a : ℂ) : ℂ := (((2)/(z))+(-1)+((-1*y)/(z))+((-1*x*a)/(z))+((-1*x*y*a)/(z))+((-1*x^2)/(z))+((-1*x^2*y)/(z)))

theorem residual403_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((1)/(y*z)))*row000 x y z a w+(((-1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((-1)/(y))+((1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((1*x^2)/(z)))*row007 x y z a w+(((-2)/(y)))*row008 x y z a w+(((1)/(z))+((-1*y)/(z))+((1*x^2)/(z))+((1*x^2*y)/(z)))*row009 x y z a w+(((1*x^2)/(y*z)))*row010 x y z a w+(((1)/(z))+((-1*y)/(z)))*row011 x y z a w+(((-1*x^2)/(y*z))+((-1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((-1)/(y))+(1))*row043 x y z a w+(((-1)/(y))+((-1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((-2)/(y*z))+((-1)/(y))+((-3)/(z)))*row319 x y z a w+((1))*row387 x y z a w+((-1))*row389 x y z a w+((-2))*row397 x y z a w+((-1))*row398 x y z a w+((1))*row403 x y z a w+((1))*row419 x y z a w+((-1))*row423 x y z a w+(((-2)/(z))+(-1)+((-1*x^2)/(z))+((-1*x^2*y)/(z)))*row427 x y z a w+(((-2*x^2)/(z)))*row428 x y z a w+(((1*x^2)/(y))+(1*x^2))*row436 x y z a w)=residual403 x y z a*w 28 := by
  dsimp only [residual403,row403,row319,row010,row038,row040,row000,row006,row043,row011,row047,row009,row427,row397,row428,row007,row008,row387,row423,row419,row398,row436,row004,row389]
  field_simp [hx,hy,hz]
  ring

def residual438 (x y z a : ℂ) : ℂ := (((-1)/(x^2*z))+((1*y)/(x^2*z))+((-1*a)/(x*z))+((1)/(z))+((-1*a^2)/(z))+((-1*x*a)/(z))+((-1*x*y*a)/(z))+((-1*x^2*y)/(z)))

theorem residual438_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((1)/(x^2*y*z))+((2*a)/(x*y*z)))*row000 x y z a w+(((1*a)/(x*y*z)))*row001 x y z a w+(((-1*a)/(x)))*row003 x y z a w+((1)+((-1*x*a)/(y))+(-1*x^2))*row004 x y z a w+(((-1*a)/(x)))*row005 x y z a w+(((-2*a)/(x))+((1*a^2)/(y))+(1*x*a))*row006 x y z a w+(((-1*y)/(z))+((1*x*y*a)/(z)))*row007 x y z a w+(((1)/(x^2))+((-1*a)/(x*y))+((-1*a)/(x)))*row008 x y z a w+(((3*y*a)/(x*z))+((-1*y)/(z))+((1*x*a)/(z))+((1*x^2*y)/(z)))*row009 x y z a w+(((1*x*a)/(y*z)))*row010 x y z a w+(((1*y*a)/(x*z)))*row011 x y z a w+(((-2*x*a)/(y*z))+((-1*x*a)/(z)))*row038 x y z a w+(((-1*a)/(x)))*row039 x y z a w+(((-1)/(x^2))+((-1*a)/(x)))*row040 x y z a w+(((-1*a)/(x)))*row043 x y z a w+(((-2*a)/(x))+(1)+((-1*x*a)/(y))+(-1*x^2))*row047 x y z a w+(((1)/(x^2)))*row049 x y z a w+(((-1)/(x^2*y*z))+((-1)/(x^2*z))+((-6*a)/(x*y*z))+((-3*a)/(x*z))+((-2*a)/(x))+((-1)/(z)))*row319 x y z a w+(((-1)/(x^2))+(1))*row387 x y z a w+(((-1*a)/(x)))*row389 x y z a w+(((-1*a)/(x))+(-1))*row397 x y z a w+(((-1*a)/(x))+(-1))*row398 x y z a w+(((1*a)/(x))+(1))*row419 x y z a w+((-1))*row423 x y z a w+(((-1)/(x^2*z))+((1*y)/(x^2*z))+((-2*a)/(x*z))+((-1*a)/(x))+((-3*y*a)/(x*z))+((-1*x*a)/(z))+((-1*x^2*y)/(z)))*row427 x y z a w+(((1*y)/(z))+((-1*x*a)/(z))+((-1*x*y*a)/(z)))*row428 x y z a w+((-1)+((1*x*a)/(y))+(1*x^2))*row436 x y z a w+((1))*row438 x y z a w)=residual438 x y z a*w 28 := by
  dsimp only [residual438,row438,row040,row000,row319,row049,row419,row001,row003,row005,row038,row010,row039,row006,row009,row043,row011,row047,row427,row397,row398,row428,row007,row008,row423,row387,row436,row004,row389]
  field_simp [hx,hy,hz]
  ring

def weightPolynomial (x y z : ℂ) : ℂ := ((-7)+(5*z)+(-1*z^2)+(2*y)+(-1*y*z)+(1*y^2)+(1*y^3)+(4*x^2)+(-1*x^2*z)+(3*x^2*y)+(1*x^2*y^2*z)+(1*x^2*y^3))

theorem resultant_zero (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hL : residual403 x y z a=0) (hQ : residual438 x y z a=0) :
    weightPolynomial x y z=0 := by
  dsimp only [residual403] at hL
  dsimp only [residual438] at hQ
  have h : (((-7)/(z^3))+((5)/(z^2))+((-1)/(z))+((2*y)/(z^3))+((-1*y)/(z^2))+((1*y^2)/(z^3))+((1*y^3)/(z^3))+((4*x^2)/(z^3))+((-1*x^2)/(z^2))+((3*x^2*y)/(z^3))+((1*x^2*y^2)/(z^2))+((1*x^2*y^3)/(z^3)))=0 := by
    linear_combination (norm := skip)
      ((((-1*x)/(z))+((-1*x*y)/(z))))^2*hQ-((((-1)/(z)))*((((-1*x)/(z))+((-1*x*y)/(z)))*a-(((2)/(z))+(-1)+((-1*y)/(z))+((-1*x^2)/(z))+((-1*x^2*y)/(z))))+(((-1)/(x*z))+((-1*x)/(z))+((-1*x*y)/(z)))*(((-1*x)/(z))+((-1*x*y)/(z))))*hL
    field_simp [hx,hy,hz]
    ring
  dsimp only [weightPolynomial]
  field_simp [hx,hy,hz] at h ⊢
  linear_combination (norm := ring_nf) h

theorem leading_constraints (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (1) (-1) (1) x y z a w r=0) :
    residual403 x y z a=0 ∧ weightPolynomial x y z=0 := by
  have hr000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hr001 : row001 x y z a w=0 := by
    rw [← row001_link]; exact hker (augmentedIndex 1)
  have hr003 : row003 x y z a w=0 := by
    rw [← row003_link]; exact hker (augmentedIndex 3)
  have hr004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hr005 : row005 x y z a w=0 := by
    rw [← row005_link]; exact hker (augmentedIndex 5)
  have hr006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hr007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hr008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hr009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hr010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hr011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hr038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hr039 : row039 x y z a w=0 := by
    rw [← row039_link]; exact hker (augmentedIndex 39)
  have hr040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hr043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hr047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hr049 : row049 x y z a w=0 := by
    rw [← row049_link]; exact hker (augmentedIndex 49)
  have hr319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hr387 : row387 x y z a w=0 := by
    rw [← row387_link]; exact hker (augmentedIndex 387)
  have hr389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hr397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hr398 : row398 x y z a w=0 := by
    rw [← row398_link]; exact hker (augmentedIndex 398)
  have hr403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hr419 : row419 x y z a w=0 := by
    rw [← row419_link]; exact hker (augmentedIndex 419)
  have hr423 : row423 x y z a w=0 := by
    rw [← row423_link]; exact hker (augmentedIndex 423)
  have hr427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hr428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hr436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hr438 : row438 x y z a w=0 := by
    rw [← row438_link]; exact hker (augmentedIndex 438)
  have h403 := residual403_identity x y z a hx hy hz w
  simp only [hr000,hr001,hr003,hr004,hr005,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr039,hr040,hr043,hr047,hr049,hr319,hr387,hr389,hr397,hr398,hr403,hr419,hr423,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h403
  have h438 := residual438_identity x y z a hx hy hz w
  simp only [hr000,hr001,hr003,hr004,hr005,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr039,hr040,hr043,hr047,hr049,hr319,hr387,hr389,hr397,hr398,hr403,hr419,hr423,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h438
  exact ⟨h403.symm,resultant_zero x y z a hx hy hz h403.symm h438.symm⟩

#print axioms leading_constraints
end SmallLevelTwentyOneWeightCase5
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightCase6
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne

def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((-1*x^2*y*z))*w 41)

theorem row000_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 0)=row000 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row000,augmentedWordRows,augmentedRow000]
  <;> ring_nf <;> simp

def row001 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((-1*y*z))*w 40)

theorem row001_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 1)=row001 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row001,augmentedWordRows,augmentedRow001]
  <;> ring_nf <;> simp

def row003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y*z)))*w 0+((1))*w 2)

theorem row003_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 3)=row003 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row003,augmentedWordRows,augmentedRow003]
  <;> ring_nf <;> simp

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*y)/(x^2*z)))*w 14)

theorem row004_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 4)=row004 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row004,augmentedWordRows,augmentedRow004]
  <;> ring_nf <;> simp

def row005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 4+(((-1*x^2)/(y*z)))*w 21)

theorem row005_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 5)=row005 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row005,augmentedWordRows,augmentedRow005]
  <;> ring_nf <;> simp

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((-1*y)/(z)))*w 28)

theorem row006_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 6)=row006 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row006,augmentedWordRows,augmentedRow006]
  <;> ring_nf <;> simp

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((-1*z)/(x^2*y)))*w 30)

theorem row007_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 7)=row007 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row007,augmentedWordRows,augmentedRow007]
  <;> ring_nf <;> simp

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((-1*x^2*y)/(z)))*w 35)

theorem row008_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 8)=row008 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row008,augmentedWordRows,augmentedRow008]
  <;> ring_nf <;> simp

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((-1*z)/(y)))*w 36)

theorem row009_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 9)=row009 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row009,augmentedWordRows,augmentedRow009]
  <;> ring_nf <;> simp

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((-1*y*z)/(x^2)))*w 38)

theorem row010_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 10)=row010 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row010,augmentedWordRows,augmentedRow010]
  <;> ring_nf <;> simp

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((-1*x^2*z)/(y)))*w 39)

theorem row011_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 11)=row011 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row011,augmentedWordRows,augmentedRow011]
  <;> ring_nf <;> simp

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

theorem row038_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 38)=row038 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row038,augmentedWordRows,augmentedRow038]
  <;> ring_nf <;> simp

def row039 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 22+((-1*x^2))*w 41)

theorem row039_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 39)=row039 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row039,augmentedWordRows,augmentedRow039]
  <;> ring_nf <;> simp

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

theorem row040_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 40)=row040 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row040,augmentedWordRows,augmentedRow040]
  <;> ring_nf <;> simp

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

theorem row043_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 43)=row043 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row043,augmentedWordRows,augmentedRow043]
  <;> ring_nf <;> simp

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

theorem row047_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 47)=row047 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row047,augmentedWordRows,augmentedRow047]
  <;> ring_nf <;> simp

def row049 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((-1*x^2))*w 5+((1))*w 16)

theorem row049_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 49)=row049 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row049,augmentedWordRows,augmentedRow049]
  <;> ring_nf <;> simp

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

theorem row319_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 319)=row319 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row319,augmentedInfinityRows,augmentedInfinity000]
  <;> ring_nf <;> simp

def row387 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+(((1)/(z)))*w 14+((1))*w 16+((1))*w 30)

theorem row387_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 387)=row387 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row387,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1*x^2)/(z)))*w 7+((1))*w 18+(((1*x^2)/(z)))*w 21+((1))*w 32)

theorem row389_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 389)=row389 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row389,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 8+(((1)/(z)))*w 28+((1))*w 36)

theorem row397_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 397)=row397 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row397,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 6+(((1)/(z)))*w 14+((1))*w 34)

theorem row398_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 398)=row398 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row398,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y)))*w 0+(((-1)/(y)))*w 6+((1))*w 8+(((-1)/(y)))*w 12+((1))*w 14+(((-1)/(y)))*w 18+((1))*w 20+(((-1)/(y)))*w 24+((1))*w 26+(((-1)/(y)))*w 30+((1))*w 32+((1))*w 38)

theorem row403_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 403)=row403 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row403,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row419 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((2))*w 6+((1))*w 8+((1))*w 10+((1))*w 12+((1))*w 14+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 28+((1))*w 30+((1))*w 32+((1))*w 34+((2))*w 36+((1))*w 38+((1))*w 40)

theorem row419_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 419)=row419 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row419,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row423 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((1))*w 6+((1))*w 10+((2))*w 12+((1))*w 14+((1))*w 16+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 26+((1))*w 28+((2))*w 30+((1))*w 32+((1))*w 36+((1))*w 38+((1))*w 40)

theorem row423_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 423)=row423 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row423,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

theorem row427_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 427)=row427 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row427,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

theorem row428_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 428)=row428 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row428,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

theorem row436_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 436)=row436 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row436,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def row438 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 5+(((-1*a)/(x)))*w 10+(((1)/(x^2)))*w 20+((1))*w 26)

theorem row438_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (-1) x y z a w (augmentedIndex 438)=row438 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row438,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def residual403 (x y z a : ℂ) : ℂ := (((-2)/(z))+(-1)+((-1*y)/(z))+((1*x*a)/(z))+((-1*x*y*a)/(z))+((1*x^2)/(z))+((-1*x^2*y)/(z)))

theorem residual403_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((1)/(y*z)))*row000 x y z a w+(((1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((1)/(y))+((-1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((-1*x^2)/(z)))*row007 x y z a w+(((2)/(y)))*row008 x y z a w+(((-1)/(z))+((-1*y)/(z))+((-1*x^2)/(z))+((1*x^2*y)/(z)))*row009 x y z a w+(((1*x^2)/(y*z)))*row010 x y z a w+(((-1)/(z))+((-1*y)/(z)))*row011 x y z a w+(((-1*x^2)/(y*z))+((1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((1)/(y))+(1))*row043 x y z a w+(((1)/(y))+((1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((-2)/(y*z))+((1)/(y))+((3)/(z)))*row319 x y z a w+((1))*row387 x y z a w+((-1))*row389 x y z a w+((-2))*row397 x y z a w+((-1))*row398 x y z a w+((1))*row403 x y z a w+((1))*row419 x y z a w+((-1))*row423 x y z a w+(((2)/(z))+(-1)+((1*x^2)/(z))+((-1*x^2*y)/(z)))*row427 x y z a w+(((2*x^2)/(z)))*row428 x y z a w+(((-1*x^2)/(y))+(1*x^2))*row436 x y z a w)=residual403 x y z a*w 28 := by
  dsimp only [residual403,row403,row319,row010,row038,row040,row000,row006,row043,row011,row047,row009,row427,row397,row428,row007,row008,row387,row423,row419,row398,row436,row004,row389]
  field_simp [hx,hy,hz]
  ring

def residual438 (x y z a : ℂ) : ℂ := (((1)/(x^2*z))+((1*y)/(x^2*z))+((1*a)/(x*z))+((-1)/(z))+((1*a^2)/(z))+((1*x*a)/(z))+((-1*x*y*a)/(z))+((-1*x^2*y)/(z)))

theorem residual438_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((1)/(x^2*y*z))+((2*a)/(x*y*z)))*row000 x y z a w+(((1*a)/(x*y*z)))*row001 x y z a w+(((-1*a)/(x)))*row003 x y z a w+((1)+((1*x*a)/(y))+(-1*x^2))*row004 x y z a w+(((-1*a)/(x)))*row005 x y z a w+(((-2*a)/(x))+((-1*a^2)/(y))+(1*x*a))*row006 x y z a w+(((-1*y)/(z))+((1*x*y*a)/(z)))*row007 x y z a w+(((1)/(x^2))+((1*a)/(x*y))+((-1*a)/(x)))*row008 x y z a w+(((3*y*a)/(x*z))+((-1*y)/(z))+((-1*x*a)/(z))+((1*x^2*y)/(z)))*row009 x y z a w+(((1*x*a)/(y*z)))*row010 x y z a w+(((1*y*a)/(x*z)))*row011 x y z a w+(((-2*x*a)/(y*z))+((1*x*a)/(z)))*row038 x y z a w+(((-1*a)/(x)))*row039 x y z a w+(((-1)/(x^2))+((-1*a)/(x)))*row040 x y z a w+(((-1*a)/(x)))*row043 x y z a w+(((-2*a)/(x))+(1)+((1*x*a)/(y))+(-1*x^2))*row047 x y z a w+(((1)/(x^2)))*row049 x y z a w+(((-1)/(x^2*y*z))+((1)/(x^2*z))+((-6*a)/(x*y*z))+((3*a)/(x*z))+((-2*a)/(x))+((1)/(z)))*row319 x y z a w+(((-1)/(x^2))+(1))*row387 x y z a w+(((-1*a)/(x)))*row389 x y z a w+(((-1*a)/(x))+(-1))*row397 x y z a w+(((-1*a)/(x))+(-1))*row398 x y z a w+(((1*a)/(x))+(1))*row419 x y z a w+((-1))*row423 x y z a w+(((1)/(x^2*z))+((1*y)/(x^2*z))+((2*a)/(x*z))+((-1*a)/(x))+((-3*y*a)/(x*z))+((1*x*a)/(z))+((-1*x^2*y)/(z)))*row427 x y z a w+(((1*y)/(z))+((1*x*a)/(z))+((-1*x*y*a)/(z)))*row428 x y z a w+((-1)+((-1*x*a)/(y))+(1*x^2))*row436 x y z a w+((1))*row438 x y z a w)=residual438 x y z a*w 28 := by
  dsimp only [residual438,row438,row040,row000,row319,row049,row419,row001,row003,row005,row038,row010,row039,row006,row009,row043,row011,row047,row427,row397,row398,row428,row007,row008,row423,row387,row436,row004,row389]
  field_simp [hx,hy,hz]
  ring

def weightPolynomial (x y z : ℂ) : ℂ := ((7)+(5*z)+(1*z^2)+(2*y)+(1*y*z)+(-1*y^2)+(1*y^3)+(-4*x^2)+(-1*x^2*z)+(3*x^2*y)+(1*x^2*y^2*z)+(1*x^2*y^3))

theorem resultant_zero (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hL : residual403 x y z a=0) (hQ : residual438 x y z a=0) :
    weightPolynomial x y z=0 := by
  dsimp only [residual403] at hL
  dsimp only [residual438] at hQ
  have h : (((7)/(z^3))+((5)/(z^2))+((1)/(z))+((2*y)/(z^3))+((1*y)/(z^2))+((-1*y^2)/(z^3))+((1*y^3)/(z^3))+((-4*x^2)/(z^3))+((-1*x^2)/(z^2))+((3*x^2*y)/(z^3))+((1*x^2*y^2)/(z^2))+((1*x^2*y^3)/(z^3)))=0 := by
    linear_combination (norm := skip)
      ((((1*x)/(z))+((-1*x*y)/(z))))^2*hQ-((((1)/(z)))*((((1*x)/(z))+((-1*x*y)/(z)))*a-(((-2)/(z))+(-1)+((-1*y)/(z))+((1*x^2)/(z))+((-1*x^2*y)/(z))))+(((1)/(x*z))+((1*x)/(z))+((-1*x*y)/(z)))*(((1*x)/(z))+((-1*x*y)/(z))))*hL
    field_simp [hx,hy,hz]
    ring
  dsimp only [weightPolynomial]
  field_simp [hx,hy,hz] at h ⊢
  linear_combination (norm := ring_nf) h

theorem leading_constraints (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (1) (1) (-1) x y z a w r=0) :
    residual403 x y z a=0 ∧ weightPolynomial x y z=0 := by
  have hr000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hr001 : row001 x y z a w=0 := by
    rw [← row001_link]; exact hker (augmentedIndex 1)
  have hr003 : row003 x y z a w=0 := by
    rw [← row003_link]; exact hker (augmentedIndex 3)
  have hr004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hr005 : row005 x y z a w=0 := by
    rw [← row005_link]; exact hker (augmentedIndex 5)
  have hr006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hr007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hr008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hr009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hr010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hr011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hr038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hr039 : row039 x y z a w=0 := by
    rw [← row039_link]; exact hker (augmentedIndex 39)
  have hr040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hr043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hr047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hr049 : row049 x y z a w=0 := by
    rw [← row049_link]; exact hker (augmentedIndex 49)
  have hr319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hr387 : row387 x y z a w=0 := by
    rw [← row387_link]; exact hker (augmentedIndex 387)
  have hr389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hr397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hr398 : row398 x y z a w=0 := by
    rw [← row398_link]; exact hker (augmentedIndex 398)
  have hr403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hr419 : row419 x y z a w=0 := by
    rw [← row419_link]; exact hker (augmentedIndex 419)
  have hr423 : row423 x y z a w=0 := by
    rw [← row423_link]; exact hker (augmentedIndex 423)
  have hr427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hr428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hr436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hr438 : row438 x y z a w=0 := by
    rw [← row438_link]; exact hker (augmentedIndex 438)
  have h403 := residual403_identity x y z a hx hy hz w
  simp only [hr000,hr001,hr003,hr004,hr005,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr039,hr040,hr043,hr047,hr049,hr319,hr387,hr389,hr397,hr398,hr403,hr419,hr423,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h403
  have h438 := residual438_identity x y z a hx hy hz w
  simp only [hr000,hr001,hr003,hr004,hr005,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr039,hr040,hr043,hr047,hr049,hr319,hr387,hr389,hr397,hr398,hr403,hr419,hr423,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h438
  exact ⟨h403.symm,resultant_zero x y z a hx hy hz h403.symm h438.symm⟩

#print axioms leading_constraints
end SmallLevelTwentyOneWeightCase6
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightCase7
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne

def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((-1*x^2*y*z))*w 41)

theorem row000_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 0)=row000 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row000,augmentedWordRows,augmentedRow000]
  <;> ring_nf <;> simp

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*y)/(x^2*z)))*w 14)

theorem row004_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 4)=row004 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row004,augmentedWordRows,augmentedRow004]
  <;> ring_nf <;> simp

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((-1*y)/(z)))*w 28)

theorem row006_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 6)=row006 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row006,augmentedWordRows,augmentedRow006]
  <;> ring_nf <;> simp

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((-1*z)/(x^2*y)))*w 30)

theorem row007_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 7)=row007 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row007,augmentedWordRows,augmentedRow007]
  <;> ring_nf <;> simp

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((-1*x^2*y)/(z)))*w 35)

theorem row008_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 8)=row008 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row008,augmentedWordRows,augmentedRow008]
  <;> ring_nf <;> simp

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((-1*z)/(y)))*w 36)

theorem row009_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 9)=row009 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row009,augmentedWordRows,augmentedRow009]
  <;> ring_nf <;> simp

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((-1*y*z)/(x^2)))*w 38)

theorem row010_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 10)=row010 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row010,augmentedWordRows,augmentedRow010]
  <;> ring_nf <;> simp

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((-1*x^2*z)/(y)))*w 39)

theorem row011_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 11)=row011 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row011,augmentedWordRows,augmentedRow011]
  <;> ring_nf <;> simp

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

theorem row038_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 38)=row038 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row038,augmentedWordRows,augmentedRow038]
  <;> ring_nf <;> simp

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

theorem row040_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 40)=row040 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row040,augmentedWordRows,augmentedRow040]
  <;> ring_nf <;> simp

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

theorem row043_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 43)=row043 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row043,augmentedWordRows,augmentedRow043]
  <;> ring_nf <;> simp

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

theorem row047_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 47)=row047 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row047,augmentedWordRows,augmentedRow047]
  <;> ring_nf <;> simp

def row049 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((-1*x^2))*w 5+((1))*w 16)

theorem row049_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 49)=row049 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row049,augmentedWordRows,augmentedRow049]
  <;> ring_nf <;> simp

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

theorem row319_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 319)=row319 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row319,augmentedInfinityRows,augmentedInfinity000]
  <;> ring_nf <;> simp

def row387 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+(((1)/(z)))*w 14+((1))*w 16+((1))*w 30)

theorem row387_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 387)=row387 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row387,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row388 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 12+((1))*w 26+(((1)/(z)))*w 28)

theorem row388_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 388)=row388 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row388,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1*x^2)/(z)))*w 7+((1))*w 18+(((1*x^2)/(z)))*w 21+((1))*w 32)

theorem row389_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 389)=row389 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row389,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row390 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 10+(((1*x^2)/(z)))*w 21+((1))*w 24+(((1*x^2)/(z)))*w 35)

theorem row390_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 390)=row390 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row390,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 8+(((1)/(z)))*w 28+((1))*w 36)

theorem row397_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 397)=row397 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row397,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y)))*w 0+(((1)/(y)))*w 6+((1))*w 8+(((1)/(y)))*w 12+((1))*w 14+(((1)/(y)))*w 18+((1))*w 20+(((1)/(y)))*w 24+((1))*w 26+(((1)/(y)))*w 30+((1))*w 32+((1))*w 38)

theorem row403_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 403)=row403 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row403,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

theorem row427_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 427)=row427 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row427,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

theorem row428_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 428)=row428 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row428,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_range_succ,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

theorem row436_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 436)=row436 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row436,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def row438 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 5+(((-1*a)/(x)))*w 10+(((1)/(x^2)))*w 20+((1))*w 26)

theorem row438_link (x y z a : ℂ) (w : Fin 42 → ℂ) :
    augmentedLaurentRow (1) (1) (1) x y z a w (augmentedIndex 438)=row438 x y z a w := by
  norm_num [augmentedIndex,augmentedLaurentRow,threePrimeMonomial,gridIndex,row438,augmentedHeckeSpecs,completeSum,Finset.sum_range_succ]
  <;> ring_nf <;> simp

def residual403 (x y z a : ℂ) : ℂ := ((-1)+((-1*y)/(z))+((1*x*a)/(z))+((-1*x*y*a)/(z))+((1*x^2)/(z))+((-1*x^2*y)/(z)))

theorem residual403_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((1)/(y*z)))*row000 x y z a w+(((1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((-1)/(y))+((-1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((1*x^2)/(z)))*row007 x y z a w+(((1)/(z))+((-1*y)/(z))+((-1*x^2)/(z))+((1*x^2*y)/(z)))*row009 x y z a w+(((1*x^2)/(y*z)))*row010 x y z a w+(((1)/(z))+((-1*y)/(z)))*row011 x y z a w+(((-1*x^2)/(y*z))+((1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((-1)/(y))+(1))*row043 x y z a w+(((-1)/(y))+((1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((-2)/(y*z))+((-1)/(y))+((3)/(z)))*row319 x y z a w+((-1))*row388 x y z a w+((-1))*row389 x y z a w+((-1))*row397 x y z a w+((1))*row403 x y z a w+((-1)+((1*x^2)/(z))+((-1*x^2*y)/(z)))*row427 x y z a w+(((-1*x^2)/(y))+(1*x^2))*row436 x y z a w)=residual403 x y z a*w 28 := by
  dsimp only [residual403,row403,row319,row010,row038,row040,row000,row006,row043,row011,row047,row009,row427,row397,row007,row388,row436,row004,row389]
  field_simp [hx,hy,hz]
  ring

def residual438 (x y z a : ℂ) : ℂ := (((1)/(x^2*z))+((1*y)/(x^2*z))+((1*a)/(x*z))+((-1)/(z))+((1*a^2)/(z))+((1*x*a)/(z))+((-1*x*y*a)/(z))+((-1*x^2*y)/(z)))

theorem residual438_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((1)/(x^2*y*z)))*row000 x y z a w+((1)+((1*x*a)/(y))+(-1*x^2))*row004 x y z a w+(((-1*a)/(x))+((-1*a^2)/(y))+(1*x*a))*row006 x y z a w+(((-1*y)/(z)))*row007 x y z a w+(((1)/(x^2))+((1*a)/(x*y)))*row008 x y z a w+(((1*y*a)/(x*z))+((-1*y)/(z))+((-1*x*a)/(z))+((1*x^2*y)/(z)))*row009 x y z a w+(((-1*x*a)/(z)))*row038 x y z a w+(((-1)/(x^2)))*row040 x y z a w+(((-1*a)/(x))+(1)+((1*x*a)/(y))+(-1*x^2))*row047 x y z a w+(((1)/(x^2)))*row049 x y z a w+(((-1)/(x^2*y*z))+((1)/(x^2*z))+((-1*a)/(x*z))+((1)/(z)))*row319 x y z a w+(((-1)/(x^2)))*row387 x y z a w+((-1))*row388 x y z a w+(((1*a)/(x)))*row390 x y z a w+(((1)/(x^2*z))+((1*y)/(x^2*z))+((1*a)/(x*z))+((-1*y*a)/(x*z))+((1*x*a)/(z))+((-1*x^2*y)/(z)))*row427 x y z a w+(((1*y)/(z)))*row428 x y z a w+((-1)+((-1*x*a)/(y))+(1*x^2))*row436 x y z a w+((1))*row438 x y z a w)=residual438 x y z a*w 28 := by
  dsimp only [residual438,row438,row040,row000,row319,row049,row387,row427,row436,row004,row006,row047,row009,row428,row007,row008,row388,row390,row038]
  field_simp [hx,hy,hz]
  ring

def weightPolynomial (x y z : ℂ) : ℂ := ((1)+(1*z)+(1*z^2)+(1*y*z)+(-1*y^2)+(1*y^3)+(-2*x^2)+(-1*x^2*z)+(3*x^2*y)+(-2*x^2*y^2)+(1*x^2*y^2*z)+(1*x^2*y^3))

theorem resultant_zero (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hL : residual403 x y z a=0) (hQ : residual438 x y z a=0) :
    weightPolynomial x y z=0 := by
  dsimp only [residual403] at hL
  dsimp only [residual438] at hQ
  have h : (((1)/(z^3))+((1)/(z^2))+((1)/(z))+((1*y)/(z^2))+((-1*y^2)/(z^3))+((1*y^3)/(z^3))+((-2*x^2)/(z^3))+((-1*x^2)/(z^2))+((3*x^2*y)/(z^3))+((-2*x^2*y^2)/(z^3))+((1*x^2*y^2)/(z^2))+((1*x^2*y^3)/(z^3)))=0 := by
    linear_combination (norm := skip)
      ((((1*x)/(z))+((-1*x*y)/(z))))^2*hQ-((((1)/(z)))*((((1*x)/(z))+((-1*x*y)/(z)))*a-((-1)+((-1*y)/(z))+((1*x^2)/(z))+((-1*x^2*y)/(z))))+(((1)/(x*z))+((1*x)/(z))+((-1*x*y)/(z)))*(((1*x)/(z))+((-1*x*y)/(z))))*hL
    field_simp [hx,hy,hz]
    ring
  dsimp only [weightPolynomial]
  field_simp [hx,hy,hz] at h ⊢
  linear_combination (norm := ring_nf) h

theorem leading_constraints (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (1) (1) (1) x y z a w r=0) :
    residual403 x y z a=0 ∧ weightPolynomial x y z=0 := by
  have hr000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hr004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hr006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hr007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hr008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hr009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hr010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hr011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hr038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hr040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hr043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hr047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hr049 : row049 x y z a w=0 := by
    rw [← row049_link]; exact hker (augmentedIndex 49)
  have hr319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hr387 : row387 x y z a w=0 := by
    rw [← row387_link]; exact hker (augmentedIndex 387)
  have hr388 : row388 x y z a w=0 := by
    rw [← row388_link]; exact hker (augmentedIndex 388)
  have hr389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hr390 : row390 x y z a w=0 := by
    rw [← row390_link]; exact hker (augmentedIndex 390)
  have hr397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hr403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hr427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hr428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hr436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hr438 : row438 x y z a w=0 := by
    rw [← row438_link]; exact hker (augmentedIndex 438)
  have h403 := residual403_identity x y z a hx hy hz w
  simp only [hr000,hr004,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr040,hr043,hr047,hr049,hr319,hr387,hr388,hr389,hr390,hr397,hr403,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h403
  have h438 := residual438_identity x y z a hx hy hz w
  simp only [hr000,hr004,hr006,hr007,hr008,hr009,hr010,hr011,hr038,hr040,hr043,hr047,hr049,hr319,hr387,hr388,hr389,hr390,hr397,hr403,hr427,hr428,hr436,hr438,h28,mul_one,mul_zero,add_zero] at h438
  exact ⟨h403.symm,resultant_zero x y z a hx hy hz h403.symm h438.symm⟩

#print axioms leading_constraints
end SmallLevelTwentyOneWeightCase7
end
