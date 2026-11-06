module
public import SmallLevelTwentyOneThirdShiftBlockModelV1
public import SmallLevelTwentyOneThirdShiftRationalTheoryV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row0000_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 0) w=row0000 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0000,Finset.sum_range_succ,augmentedWordRows,augmentedRow000]
  <;> ring_nf <;> simp

#print axioms row0000_link

theorem row0001_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 1) w=row0001 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0001,Finset.sum_range_succ,augmentedWordRows,augmentedRow001]
  <;> ring_nf <;> simp

#print axioms row0001_link

theorem row0002_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 2) w=row0002 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0002,Finset.sum_range_succ,augmentedWordRows,augmentedRow002]
  <;> ring_nf <;> simp

#print axioms row0002_link

theorem row0003_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 3) w=row0003 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0003,Finset.sum_range_succ,augmentedWordRows,augmentedRow003]
  <;> ring_nf <;> simp

#print axioms row0003_link

theorem row0004_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 4) w=row0004 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0004,Finset.sum_range_succ,augmentedWordRows,augmentedRow004]
  <;> ring_nf <;> simp

#print axioms row0004_link

theorem row0005_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 5) w=row0005 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0005,Finset.sum_range_succ,augmentedWordRows,augmentedRow005]
  <;> ring_nf <;> simp

#print axioms row0005_link

theorem row0006_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 6) w=row0006 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0006,Finset.sum_range_succ,augmentedWordRows,augmentedRow006]
  <;> ring_nf <;> simp

#print axioms row0006_link

theorem row0007_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 7) w=row0007 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0007,Finset.sum_range_succ,augmentedWordRows,augmentedRow007]
  <;> ring_nf <;> simp

#print axioms row0007_link

theorem row0008_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 8) w=row0008 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0008,Finset.sum_range_succ,augmentedWordRows,augmentedRow008]
  <;> ring_nf <;> simp

#print axioms row0008_link

theorem row0009_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 9) w=row0009 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0009,Finset.sum_range_succ,augmentedWordRows,augmentedRow009]
  <;> ring_nf <;> simp

#print axioms row0009_link

theorem row0010_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 10) w=row0010 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0010,Finset.sum_range_succ,augmentedWordRows,augmentedRow010]
  <;> ring_nf <;> simp

#print axioms row0010_link

theorem row0011_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 11) w=row0011 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0011,Finset.sum_range_succ,augmentedWordRows,augmentedRow011]
  <;> ring_nf <;> simp

#print axioms row0011_link

end SmallLevelTwentyOneThirdShiftLinks
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row0038_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 38) w=row0038 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0038,Finset.sum_range_succ,augmentedWordRows,augmentedRow038]
  <;> ring_nf <;> simp

#print axioms row0038_link

theorem row0039_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 39) w=row0039 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0039,Finset.sum_range_succ,augmentedWordRows,augmentedRow039]
  <;> ring_nf <;> simp

#print axioms row0039_link

theorem row0040_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 40) w=row0040 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0040,Finset.sum_range_succ,augmentedWordRows,augmentedRow040]
  <;> ring_nf <;> simp

#print axioms row0040_link

theorem row0043_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 43) w=row0043 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0043,Finset.sum_range_succ,augmentedWordRows,augmentedRow043]
  <;> ring_nf <;> simp

#print axioms row0043_link

theorem row0046_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 46) w=row0046 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0046,Finset.sum_range_succ,augmentedWordRows,augmentedRow046]
  <;> ring_nf <;> simp

#print axioms row0046_link

theorem row0047_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 47) w=row0047 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0047,Finset.sum_range_succ,augmentedWordRows,augmentedRow047]
  <;> ring_nf <;> simp

#print axioms row0047_link

theorem row0048_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 48) w=row0048 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0048,Finset.sum_range_succ,augmentedWordRows,augmentedRow048]
  <;> ring_nf <;> simp

#print axioms row0048_link

theorem row0049_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 49) w=row0049 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0049,Finset.sum_range_succ,augmentedWordRows,augmentedRow049]
  <;> ring_nf <;> simp

#print axioms row0049_link

theorem row0051_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 51) w=row0051 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0051,Finset.sum_range_succ,augmentedWordRows,augmentedRow051]
  <;> ring_nf <;> simp

#print axioms row0051_link

theorem row0319_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 319) w=row0319 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0319,Finset.sum_range_succ,augmentedInfinityRows,augmentedInfinity000]
  <;> ring_nf <;> simp

#print axioms row0319_link

theorem row0385_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 385) w=row0385 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0385,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0385_link

theorem row0386_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 386) w=row0386 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0386,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0386_link

end SmallLevelTwentyOneThirdShiftLinks
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row0387_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 387) w=row0387 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0387,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0387_link

theorem row0388_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 388) w=row0388 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0388,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0388_link

theorem row0389_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 389) w=row0389 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0389,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0389_link

theorem row0390_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 390) w=row0390 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0390,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0390_link

theorem row0397_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 397) w=row0397 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0397,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0397_link

theorem row0398_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 398) w=row0398 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0398,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0398_link

theorem row0401_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 401) w=row0401 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0401,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0401_link

theorem row0402_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 402) w=row0402 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0402,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0402_link

theorem row0403_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 403) w=row0403 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0403,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0403_link

theorem row0404_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 404) w=row0404 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0404,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0404_link

theorem row0405_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 405) w=row0405 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0405,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0405_link

theorem row0427_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 427) w=row0427 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0427,Finset.sum_range_succ,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0427_link

end SmallLevelTwentyOneThirdShiftLinks
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row0437_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 437) w=row0437 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0437,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row0437_link

theorem row0439_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 439) w=row0439 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0439,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row0439_link

theorem row0441_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 441) w=row0441 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0441,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row0441_link

theorem row0442_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 442) w=row0442 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0442,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row0442_link

theorem row0444_link (w : Fin 168 → ℂ) :
    jetBlockRow 0 (augmentedIndex 444) w=row0444 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0444,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row0444_link

theorem row0474_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 0) w=row0474 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0474,Finset.sum_range_succ,augmentedWordRows,augmentedRow000]
  <;> ring_nf <;> simp

#print axioms row0474_link

theorem row0475_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 1) w=row0475 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0475,Finset.sum_range_succ,augmentedWordRows,augmentedRow001]
  <;> ring_nf <;> simp

#print axioms row0475_link

theorem row0476_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 2) w=row0476 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0476,Finset.sum_range_succ,augmentedWordRows,augmentedRow002]
  <;> ring_nf <;> simp

#print axioms row0476_link

theorem row0477_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 3) w=row0477 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0477,Finset.sum_range_succ,augmentedWordRows,augmentedRow003]
  <;> ring_nf <;> simp

#print axioms row0477_link

theorem row0478_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 4) w=row0478 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0478,Finset.sum_range_succ,augmentedWordRows,augmentedRow004]
  <;> ring_nf <;> simp

#print axioms row0478_link

theorem row0479_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 5) w=row0479 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0479,Finset.sum_range_succ,augmentedWordRows,augmentedRow005]
  <;> ring_nf <;> simp

#print axioms row0479_link

theorem row0480_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 6) w=row0480 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0480,Finset.sum_range_succ,augmentedWordRows,augmentedRow006]
  <;> ring_nf <;> simp

#print axioms row0480_link

end SmallLevelTwentyOneThirdShiftLinks
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row0481_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 7) w=row0481 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0481,Finset.sum_range_succ,augmentedWordRows,augmentedRow007]
  <;> ring_nf <;> simp

#print axioms row0481_link

theorem row0482_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 8) w=row0482 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0482,Finset.sum_range_succ,augmentedWordRows,augmentedRow008]
  <;> ring_nf <;> simp

#print axioms row0482_link

theorem row0483_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 9) w=row0483 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0483,Finset.sum_range_succ,augmentedWordRows,augmentedRow009]
  <;> ring_nf <;> simp

#print axioms row0483_link

theorem row0484_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 10) w=row0484 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0484,Finset.sum_range_succ,augmentedWordRows,augmentedRow010]
  <;> ring_nf <;> simp

#print axioms row0484_link

theorem row0485_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 11) w=row0485 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0485,Finset.sum_range_succ,augmentedWordRows,augmentedRow011]
  <;> ring_nf <;> simp

#print axioms row0485_link

theorem row0512_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 38) w=row0512 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0512,Finset.sum_range_succ,augmentedWordRows,augmentedRow038]
  <;> ring_nf <;> simp

#print axioms row0512_link

theorem row0513_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 39) w=row0513 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0513,Finset.sum_range_succ,augmentedWordRows,augmentedRow039]
  <;> ring_nf <;> simp

#print axioms row0513_link

theorem row0514_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 40) w=row0514 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0514,Finset.sum_range_succ,augmentedWordRows,augmentedRow040]
  <;> ring_nf <;> simp

#print axioms row0514_link

theorem row0517_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 43) w=row0517 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0517,Finset.sum_range_succ,augmentedWordRows,augmentedRow043]
  <;> ring_nf <;> simp

#print axioms row0517_link

theorem row0520_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 46) w=row0520 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0520,Finset.sum_range_succ,augmentedWordRows,augmentedRow046]
  <;> ring_nf <;> simp

#print axioms row0520_link

theorem row0521_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 47) w=row0521 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0521,Finset.sum_range_succ,augmentedWordRows,augmentedRow047]
  <;> ring_nf <;> simp

#print axioms row0521_link

theorem row0522_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 48) w=row0522 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0522,Finset.sum_range_succ,augmentedWordRows,augmentedRow048]
  <;> ring_nf <;> simp

#print axioms row0522_link

end SmallLevelTwentyOneThirdShiftLinks
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row0523_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 49) w=row0523 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0523,Finset.sum_range_succ,augmentedWordRows,augmentedRow049]
  <;> ring_nf <;> simp

#print axioms row0523_link

theorem row0525_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 51) w=row0525 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0525,Finset.sum_range_succ,augmentedWordRows,augmentedRow051]
  <;> ring_nf <;> simp

#print axioms row0525_link

theorem row0793_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 319) w=row0793 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0793,Finset.sum_range_succ,augmentedInfinityRows,augmentedInfinity000]
  <;> ring_nf <;> simp

#print axioms row0793_link

theorem row0859_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 385) w=row0859 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0859,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0859_link

theorem row0860_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 386) w=row0860 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0860,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0860_link

theorem row0861_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 387) w=row0861 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0861,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0861_link

theorem row0862_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 388) w=row0862 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0862,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0862_link

theorem row0863_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 389) w=row0863 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0863,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0863_link

theorem row0864_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 390) w=row0864 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0864,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0864_link

theorem row0871_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 397) w=row0871 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0871,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0871_link

theorem row0872_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 398) w=row0872 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0872,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0872_link

theorem row0875_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 401) w=row0875 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0875,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0875_link

end SmallLevelTwentyOneThirdShiftLinks
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row0876_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 402) w=row0876 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0876,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0876_link

theorem row0877_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 403) w=row0877 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0877,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0877_link

theorem row0878_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 404) w=row0878 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0878,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0878_link

theorem row0879_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 405) w=row0879 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0879,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0879_link

theorem row0901_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 427) w=row0901 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0901,Finset.sum_range_succ,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row0901_link

theorem row0910_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 436) w=row0910 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0910,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row0910_link

theorem row0911_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 437) w=row0911 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0911,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row0911_link

theorem row0913_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 439) w=row0913 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0913,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row0913_link

theorem row0915_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 441) w=row0915 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0915,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row0915_link

theorem row0916_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 442) w=row0916 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0916,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row0916_link

theorem row0918_link (w : Fin 168 → ℂ) :
    jetBlockRow 1 (augmentedIndex 444) w=row0918 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0918,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row0918_link

theorem row0948_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 0) w=row0948 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0948,Finset.sum_range_succ,augmentedWordRows,augmentedRow000]
  <;> ring_nf <;> simp

#print axioms row0948_link

end SmallLevelTwentyOneThirdShiftLinks
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row0949_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 1) w=row0949 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0949,Finset.sum_range_succ,augmentedWordRows,augmentedRow001]
  <;> ring_nf <;> simp

#print axioms row0949_link

theorem row0950_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 2) w=row0950 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0950,Finset.sum_range_succ,augmentedWordRows,augmentedRow002]
  <;> ring_nf <;> simp

#print axioms row0950_link

theorem row0951_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 3) w=row0951 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0951,Finset.sum_range_succ,augmentedWordRows,augmentedRow003]
  <;> ring_nf <;> simp

#print axioms row0951_link

theorem row0952_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 4) w=row0952 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0952,Finset.sum_range_succ,augmentedWordRows,augmentedRow004]
  <;> ring_nf <;> simp

#print axioms row0952_link

theorem row0953_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 5) w=row0953 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0953,Finset.sum_range_succ,augmentedWordRows,augmentedRow005]
  <;> ring_nf <;> simp

#print axioms row0953_link

theorem row0954_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 6) w=row0954 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0954,Finset.sum_range_succ,augmentedWordRows,augmentedRow006]
  <;> ring_nf <;> simp

#print axioms row0954_link

theorem row0955_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 7) w=row0955 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0955,Finset.sum_range_succ,augmentedWordRows,augmentedRow007]
  <;> ring_nf <;> simp

#print axioms row0955_link

theorem row0956_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 8) w=row0956 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0956,Finset.sum_range_succ,augmentedWordRows,augmentedRow008]
  <;> ring_nf <;> simp

#print axioms row0956_link

theorem row0957_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 9) w=row0957 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0957,Finset.sum_range_succ,augmentedWordRows,augmentedRow009]
  <;> ring_nf <;> simp

#print axioms row0957_link

theorem row0958_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 10) w=row0958 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0958,Finset.sum_range_succ,augmentedWordRows,augmentedRow010]
  <;> ring_nf <;> simp

#print axioms row0958_link

theorem row0959_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 11) w=row0959 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0959,Finset.sum_range_succ,augmentedWordRows,augmentedRow011]
  <;> ring_nf <;> simp

#print axioms row0959_link

theorem row0986_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 38) w=row0986 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0986,Finset.sum_range_succ,augmentedWordRows,augmentedRow038]
  <;> ring_nf <;> simp

#print axioms row0986_link

end SmallLevelTwentyOneThirdShiftLinks
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row0987_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 39) w=row0987 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0987,Finset.sum_range_succ,augmentedWordRows,augmentedRow039]
  <;> ring_nf <;> simp

#print axioms row0987_link

theorem row0988_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 40) w=row0988 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0988,Finset.sum_range_succ,augmentedWordRows,augmentedRow040]
  <;> ring_nf <;> simp

#print axioms row0988_link

theorem row0991_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 43) w=row0991 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0991,Finset.sum_range_succ,augmentedWordRows,augmentedRow043]
  <;> ring_nf <;> simp

#print axioms row0991_link

theorem row0994_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 46) w=row0994 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0994,Finset.sum_range_succ,augmentedWordRows,augmentedRow046]
  <;> ring_nf <;> simp

#print axioms row0994_link

theorem row0995_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 47) w=row0995 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0995,Finset.sum_range_succ,augmentedWordRows,augmentedRow047]
  <;> ring_nf <;> simp

#print axioms row0995_link

theorem row0996_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 48) w=row0996 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0996,Finset.sum_range_succ,augmentedWordRows,augmentedRow048]
  <;> ring_nf <;> simp

#print axioms row0996_link

theorem row0997_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 49) w=row0997 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0997,Finset.sum_range_succ,augmentedWordRows,augmentedRow049]
  <;> ring_nf <;> simp

#print axioms row0997_link

theorem row0999_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 51) w=row0999 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row0999,Finset.sum_range_succ,augmentedWordRows,augmentedRow051]
  <;> ring_nf <;> simp

#print axioms row0999_link

theorem row1267_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 319) w=row1267 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1267,Finset.sum_range_succ,augmentedInfinityRows,augmentedInfinity000]
  <;> ring_nf <;> simp

#print axioms row1267_link

theorem row1333_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 385) w=row1333 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1333,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1333_link

theorem row1334_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 386) w=row1334 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1334,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1334_link

theorem row1335_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 387) w=row1335 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1335,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1335_link

end SmallLevelTwentyOneThirdShiftLinks
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row1336_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 388) w=row1336 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1336,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1336_link

theorem row1337_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 389) w=row1337 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1337,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1337_link

theorem row1338_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 390) w=row1338 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1338,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1338_link

theorem row1345_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 397) w=row1345 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1345,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1345_link

theorem row1346_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 398) w=row1346 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1346,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1346_link

theorem row1349_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 401) w=row1349 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1349,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1349_link

theorem row1350_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 402) w=row1350 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1350,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1350_link

theorem row1351_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 403) w=row1351 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1351,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1351_link

theorem row1352_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 404) w=row1352 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1352,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1352_link

theorem row1353_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 405) w=row1353 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1353,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1353_link

theorem row1375_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 427) w=row1375 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1375,Finset.sum_range_succ,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1375_link

theorem row1384_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 436) w=row1384 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1384,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row1384_link

end SmallLevelTwentyOneThirdShiftLinks
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row1385_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 437) w=row1385 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1385,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row1385_link

theorem row1387_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 439) w=row1387 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1387,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row1387_link

theorem row1389_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 441) w=row1389 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1389,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row1389_link

theorem row1390_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 442) w=row1390 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1390,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row1390_link

theorem row1392_link (w : Fin 168 → ℂ) :
    jetBlockRow 2 (augmentedIndex 444) w=row1392 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1392,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row1392_link

theorem row1422_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 0) w=row1422 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1422,Finset.sum_range_succ,augmentedWordRows,augmentedRow000]
  <;> ring_nf <;> simp

#print axioms row1422_link

theorem row1423_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 1) w=row1423 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1423,Finset.sum_range_succ,augmentedWordRows,augmentedRow001]
  <;> ring_nf <;> simp

#print axioms row1423_link

theorem row1424_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 2) w=row1424 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1424,Finset.sum_range_succ,augmentedWordRows,augmentedRow002]
  <;> ring_nf <;> simp

#print axioms row1424_link

theorem row1425_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 3) w=row1425 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1425,Finset.sum_range_succ,augmentedWordRows,augmentedRow003]
  <;> ring_nf <;> simp

#print axioms row1425_link

theorem row1426_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 4) w=row1426 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1426,Finset.sum_range_succ,augmentedWordRows,augmentedRow004]
  <;> ring_nf <;> simp

#print axioms row1426_link

theorem row1427_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 5) w=row1427 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1427,Finset.sum_range_succ,augmentedWordRows,augmentedRow005]
  <;> ring_nf <;> simp

#print axioms row1427_link

theorem row1428_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 6) w=row1428 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1428,Finset.sum_range_succ,augmentedWordRows,augmentedRow006]
  <;> ring_nf <;> simp

#print axioms row1428_link

end SmallLevelTwentyOneThirdShiftLinks
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row1429_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 7) w=row1429 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1429,Finset.sum_range_succ,augmentedWordRows,augmentedRow007]
  <;> ring_nf <;> simp

#print axioms row1429_link

theorem row1430_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 8) w=row1430 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1430,Finset.sum_range_succ,augmentedWordRows,augmentedRow008]
  <;> ring_nf <;> simp

#print axioms row1430_link

theorem row1431_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 9) w=row1431 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1431,Finset.sum_range_succ,augmentedWordRows,augmentedRow009]
  <;> ring_nf <;> simp

#print axioms row1431_link

theorem row1432_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 10) w=row1432 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1432,Finset.sum_range_succ,augmentedWordRows,augmentedRow010]
  <;> ring_nf <;> simp

#print axioms row1432_link

theorem row1433_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 11) w=row1433 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1433,Finset.sum_range_succ,augmentedWordRows,augmentedRow011]
  <;> ring_nf <;> simp

#print axioms row1433_link

theorem row1460_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 38) w=row1460 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1460,Finset.sum_range_succ,augmentedWordRows,augmentedRow038]
  <;> ring_nf <;> simp

#print axioms row1460_link

theorem row1461_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 39) w=row1461 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1461,Finset.sum_range_succ,augmentedWordRows,augmentedRow039]
  <;> ring_nf <;> simp

#print axioms row1461_link

theorem row1462_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 40) w=row1462 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1462,Finset.sum_range_succ,augmentedWordRows,augmentedRow040]
  <;> ring_nf <;> simp

#print axioms row1462_link

theorem row1465_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 43) w=row1465 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1465,Finset.sum_range_succ,augmentedWordRows,augmentedRow043]
  <;> ring_nf <;> simp

#print axioms row1465_link

theorem row1468_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 46) w=row1468 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1468,Finset.sum_range_succ,augmentedWordRows,augmentedRow046]
  <;> ring_nf <;> simp

#print axioms row1468_link

theorem row1469_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 47) w=row1469 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1469,Finset.sum_range_succ,augmentedWordRows,augmentedRow047]
  <;> ring_nf <;> simp

#print axioms row1469_link

theorem row1470_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 48) w=row1470 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1470,Finset.sum_range_succ,augmentedWordRows,augmentedRow048]
  <;> ring_nf <;> simp

#print axioms row1470_link

end SmallLevelTwentyOneThirdShiftLinks
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row1471_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 49) w=row1471 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1471,Finset.sum_range_succ,augmentedWordRows,augmentedRow049]
  <;> ring_nf <;> simp

#print axioms row1471_link

theorem row1473_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 51) w=row1473 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1473,Finset.sum_range_succ,augmentedWordRows,augmentedRow051]
  <;> ring_nf <;> simp

#print axioms row1473_link

theorem row1741_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 319) w=row1741 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1741,Finset.sum_range_succ,augmentedInfinityRows,augmentedInfinity000]
  <;> ring_nf <;> simp

#print axioms row1741_link

theorem row1807_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 385) w=row1807 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1807,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1807_link

theorem row1808_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 386) w=row1808 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1808,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1808_link

theorem row1809_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 387) w=row1809 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1809,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1809_link

theorem row1810_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 388) w=row1810 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1810,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1810_link

theorem row1811_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 389) w=row1811 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1811,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1811_link

theorem row1812_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 390) w=row1812 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1812,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1812_link

theorem row1819_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 397) w=row1819 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1819,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1819_link

theorem row1820_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 398) w=row1820 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1820,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1820_link

theorem row1823_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 401) w=row1823 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1823,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1823_link

end SmallLevelTwentyOneThirdShiftLinks
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The generated finite arithmetic checks close at different tactic stages.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneThirdShiftLinks
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne SmallLevelFiniteShift
open SmallLevelTwentyOneThirdShiftRational

theorem row1824_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 402) w=row1824 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1824,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1824_link

theorem row1825_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 403) w=row1825 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1825,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1825_link

theorem row1826_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 404) w=row1826 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1826,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1826_link

theorem row1827_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 405) w=row1827 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1827,Finset.sum_range_succ,augmentedTaylorSpecs,augmentedTaylorPowers,localRoot,sampleSum,FinitenessRamanujanSum.residues,ramanujanSlope,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1827_link

theorem row1849_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 427) w=row1849 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1849,Finset.sum_range_succ,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1849_link

theorem row1850_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 428) w=row1850 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1850,Finset.sum_range_succ,augmentedEntireSpecs,sampleSum,FinitenessRamanujanSum.residues,Finset.sum_filter,Nat.Coprime]
  <;> ring_nf <;> simp

#print axioms row1850_link

theorem row1858_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 436) w=row1858 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1858,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row1858_link

theorem row1859_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 437) w=row1859 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1859,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row1859_link

theorem row1861_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 439) w=row1861 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1861,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row1861_link

theorem row1863_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 441) w=row1863 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1863,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row1863_link

theorem row1864_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 442) w=row1864 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1864,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row1864_link

theorem row1866_link (w : Fin 168 → ℂ) :
    jetBlockRow 3 (augmentedIndex 444) w=row1866 w := by
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,augmentedIndex,augmentedLaurentRow,augmentedLaurentTaylorRow,threePrimeMonomial,gridIndex,row1866,Finset.sum_range_succ,augmentedHeckeSpecs,completeSum]
  <;> ring_nf <;> simp

#print axioms row1866_link

end SmallLevelTwentyOneThirdShiftLinks
end
