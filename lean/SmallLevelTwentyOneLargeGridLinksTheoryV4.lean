module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import SmallLevelTwentyOneAugmentedLaurentModelV1
public import SmallLevelTwentyOneChiFiveShiftGeometryV1
public import SmallLevelTwentyOneFiniteGridTheoryV4
public import SmallLevelTwentyOneLargeGridAlgebraTheoryV4
public import SmallLevelTwentyOneLargeGridDataTheoryV4
public import SmallLevelTwentyOneLargeGridMatrixSourcesV1
public import SmallLevelTwentyOneLargeGridRowDataV1

/-! Consolidated chapter: SmallLevelTwentyOneLargeGridLinks. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyOneLargeGridOtherLinksBundleV4 -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyOneLargeGridLinks
open Complex SmallLevelTwentyOneFiniteGrid SmallLevelTwentyOneLargeGridAlgebra
open SmallLevelTwentyOneKnownWords

theorem other_link5 (x y z b : ℂ) (v : Fin 210 → ℂ) :
    source5 x y z b v=v (gridIndex 210 (by decide) (0)) := by
  norm_num [source5,sampleSum,completeSum,gridIndex,FinitenessRamanujanSum.residues,
    Finset.sum_filter,Finset.sum_range_succ]
  <;> ring_nf <;> simp
#print axioms other_link5

theorem other_link125 (x y z b : ℂ) (v : Fin 210 → ℂ) :
    source125 x y z b v=v (gridIndex 210 (by decide) (106)) := by
  norm_num [source125,sampleSum,completeSum,gridIndex,FinitenessRamanujanSum.residues,
    Finset.sum_filter,Finset.sum_range_succ]
  <;> ring_nf <;> simp
#print axioms other_link125

theorem other_link1451 (x y z b : ℂ) (v : Fin 210 → ℂ) :
    source1451 x y z b v=v (gridIndex 210 (by decide) (5*(3))) := by
  norm_num [source1451,sampleSum,completeSum,gridIndex,FinitenessRamanujanSum.residues,
    Finset.sum_filter,Finset.sum_range_succ]
  <;> ring_nf <;> simp
#print axioms other_link1451

theorem other_link1037 (x y z b : ℂ) (v : Fin 210 → ℂ) :
    source1037 x y z b v=sampleSum 210 (by decide) 3 0 v := by
  norm_num [source1037,sampleSum,completeSum,gridIndex,FinitenessRamanujanSum.residues,
    Finset.sum_filter,Finset.sum_range_succ]
  <;> ring_nf <;> simp
#print axioms other_link1037

theorem other_link1246 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1246 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (3) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1246,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1246

theorem other_link1099 (x y z b : ℂ) (v : Fin 210 → ℂ) :
    source1099 x y z b v=sampleSum 210 (by decide) 6 0 v := by
  norm_num [source1099,sampleSum,completeSum,gridIndex,FinitenessRamanujanSum.residues,
    Finset.sum_filter,Finset.sum_range_succ]
  <;> ring_nf <;> simp
#print axioms other_link1099

theorem other_link1247 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1247 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (4) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1247,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1247

theorem other_link1252 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1252 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (9) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1252,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1252

theorem other_link1257 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1257 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (14) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1257,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1257

theorem other_link1271 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1271 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (28) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1271,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1271

theorem other_link1149 (x y z b : ℂ) (v : Fin 210 → ℂ) :
    source1149 x y z b v=sampleSum 210 (by decide) 10 0 v := by
  norm_num [source1149,sampleSum,completeSum,gridIndex,FinitenessRamanujanSum.residues,
    Finset.sum_filter,Finset.sum_range_succ]
  <;> ring_nf <;> simp
#print axioms other_link1149

theorem other_link1292 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1292 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (49) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1292,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1292

theorem other_link1294 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1294 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (51) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1294,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1294

theorem other_link1298 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1298 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (55) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1298,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1298

theorem other_link1299 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1299 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (56) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1299,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1299

theorem other_link1203 (x y z b : ℂ) (v : Fin 210 → ℂ) :
    source1203 x y z b v=sampleSum 210 (by decide) 30 0 v := by
  norm_num [source1203,sampleSum,completeSum,gridIndex,FinitenessRamanujanSum.residues,
    Finset.sum_filter,Finset.sum_range_succ]
  <;> ring_nf <;> simp
#print axioms other_link1203

theorem other_link1261 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1261 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (18) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1261,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1261

theorem other_link1279 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1279 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (36) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1279,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1279

theorem other_link1339 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1339 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (96) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1339,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1339

theorem other_link1277 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1277 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (34) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1277,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1277

theorem other_link1297 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1297 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (54) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1297,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1297

theorem other_link1330 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1330 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (87) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1330,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1330

theorem other_link1251 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1251 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (8) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1251,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1251

theorem other_link1254 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1254 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (11) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1254,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1254

theorem other_link1255 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1255 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (12) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1255,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1255

theorem other_link1260 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1260 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (17) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1260,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1260

theorem other_link1267 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1267 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (24) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1267,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1267

theorem other_link1270 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1270 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (27) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1270,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1270

theorem other_link1276 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1276 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (33) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1276,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1276

theorem other_link1280 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1280 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (37) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1280,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1280

theorem other_link1282 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1282 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (39) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1282,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1282

theorem other_link1291 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1291 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (48) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1291,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1291

theorem other_link1295 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1295 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (52) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1295,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1295

theorem other_link1296 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1296 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (53) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1296,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1296

theorem other_link1300 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1300 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (57) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1300,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1300

theorem other_link1311 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1311 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (68) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1311,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1311

theorem other_link1321 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1321 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (78) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1321,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1321

theorem other_link1331 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1331 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (88) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1331,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1331

theorem other_link1337 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1337 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (94) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1337,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1337

theorem other_link1340 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1340 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (97) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1340,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1340

theorem other_link1351 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1351 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (3) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1351,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1351

theorem other_link1354 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1354 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (6) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1354,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1354

theorem other_link1356 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1356 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (8) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1356,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1356

theorem other_link1359 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1359 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (11) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1359,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1359

theorem other_link1360 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1360 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (12) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1360,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1360

theorem other_link1364 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1364 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (16) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1364,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1364

theorem other_link1317 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1317 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (74) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1317,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1317

theorem other_link1365 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1365 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (17) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1365,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1365

theorem other_link1366 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1366 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (18) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1366,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1366

theorem other_link1367 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1367 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (19) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1367,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1367

theorem other_link1370 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1370 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (22) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1370,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1370

theorem other_link1329 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1329 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (86) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1329,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1329

theorem other_link1286 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1286 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (43) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1286,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1286

theorem other_link1372 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1372 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (24) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1372,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1372

theorem other_link1377 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1377 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (29) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1377,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1377

theorem other_link1379 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1379 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (31) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1379,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1379

theorem other_link1380 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1380 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (32) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1380,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1380

theorem other_link1259 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1259 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (16) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1259,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1259

theorem other_link1381 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1381 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (33) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1381,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1381

theorem other_link1274 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1274 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (31) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1274,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1274

theorem other_link1262 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1262 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (19) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1262,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1262

theorem other_link1305 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1305 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (62) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1305,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1305

theorem other_link1332 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1332 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (89) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1332,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1332

theorem other_link1389 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1389 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (41) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1389,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1389

theorem other_link1394 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1394 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (46) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1394,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1394

theorem other_link1406 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1406 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (58) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1406,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1406

theorem other_link1407 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1407 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (59) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1407,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1407

theorem other_link1415 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1415 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 3 (67) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1415,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1415

theorem other_link1509 (x y z b : ℂ) (v : Fin 210 → ℂ) :
    source1509 x y z b v=completeSum 210 (by decide) 5 (19) v := by
  norm_num [source1509,sampleSum,completeSum,gridIndex,FinitenessRamanujanSum.residues,
    Finset.sum_filter,Finset.sum_range_succ]
  <;> ring_nf <;> simp
#print axioms other_link1509

theorem other_link1513 (x y z b : ℂ) (v : Fin 210 → ℂ) :
    source1513 x y z b v=completeSum 210 (by decide) 5 (23) v := by
  norm_num [source1513,sampleSum,completeSum,gridIndex,FinitenessRamanujanSum.residues,
    Finset.sum_filter,Finset.sum_range_succ]
  <;> ring_nf <;> simp
#print axioms other_link1513

theorem other_link1256 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1256 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (13) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1256,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1256

theorem other_link1265 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1265 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (22) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1265,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1265

theorem other_link1275 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1275 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (32) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1275,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1275

theorem other_link1281 (f : ℕ → ℂ)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (s : ℂ) (v : Fin 210 → ℂ) :
    source1281 (primeParameter 2 1 s) (primeParameter 3 1 s)
      (primeParameter 7 1 s) (primeParameter 5 1 s) v=
        fullHeckeRow 210 (by decide) 1 f 2 (38) s v := by
  have h2 : (2:ℂ)^(1-s)=(primeParameter 2 1 s)⁻¹ := by simpa using primeParameter_inverse 2 1 s
  have h3 : (3:ℂ)^(1-s)=(primeParameter 3 1 s)⁻¹ := by simpa using primeParameter_inverse 3 1 s
  have h7 : (7:ℂ)^(1-s)=(primeParameter 7 1 s)⁻¹ := by simpa using primeParameter_inverse 7 1 s
  have hu' : (Real.sqrt 3:ℂ)*f 3= -1 := (SmallLevelTwentyOne.rootU_eigenvalue f).symm.trans hu
  have hv' : (Real.sqrt 7:ℂ)*f 7=1 := (SmallLevelTwentyOne.rootV_eigenvalue f).symm.trans hv
  norm_num [source1281,fullHeckeRow,completeSum,gridIndex,Finset.sum_range_succ,
    h2,h3,h7,ha,hu',hv']
  <;> ring_nf <;> simp
#print axioms other_link1281

end SmallLevelTwentyOneLargeGridLinks
end
end

/-! ## SmallLevelTwentyOneLargeGridWordLinksBundleV4 -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyOneLargeGridLinks
open Complex SmallLevelTwentyOneFiniteGrid SmallLevelTwentyOneLargeGridData
open SmallLevelTwentyOneLargeGridAlgebra SmallLevelTwentyOneKnownWords

theorem word_link0 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source0 x y z b v=
      v (gridIndex 210 (by decide) wordRow0.source)-
        (-1:ℂ)^wordRow0.count*fourPrimeMonomial wordRow0.powers x y z b*
          v (gridIndex 210 (by decide) wordRow0.target) := by
  norm_num [source0,gridIndex,wordRow0,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link0
theorem word_link2 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source2 x y z b v=
      v (gridIndex 210 (by decide) wordRow2.source)-
        (-1:ℂ)^wordRow2.count*fourPrimeMonomial wordRow2.powers x y z b*
          v (gridIndex 210 (by decide) wordRow2.target) := by
  norm_num [source2,gridIndex,wordRow2,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link2
theorem word_link6 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source6 x y z b v=
      v (gridIndex 210 (by decide) wordRow6.source)-
        (-1:ℂ)^wordRow6.count*fourPrimeMonomial wordRow6.powers x y z b*
          v (gridIndex 210 (by decide) wordRow6.target) := by
  norm_num [source6,gridIndex,wordRow6,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link6
theorem word_link7 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source7 x y z b v=
      v (gridIndex 210 (by decide) wordRow7.source)-
        (-1:ℂ)^wordRow7.count*fourPrimeMonomial wordRow7.powers x y z b*
          v (gridIndex 210 (by decide) wordRow7.target) := by
  norm_num [source7,gridIndex,wordRow7,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link7
theorem word_link10 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source10 x y z b v=
      v (gridIndex 210 (by decide) wordRow10.source)-
        (-1:ℂ)^wordRow10.count*fourPrimeMonomial wordRow10.powers x y z b*
          v (gridIndex 210 (by decide) wordRow10.target) := by
  norm_num [source10,gridIndex,wordRow10,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link10
theorem word_link13 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source13 x y z b v=
      v (gridIndex 210 (by decide) wordRow13.source)-
        (-1:ℂ)^wordRow13.count*fourPrimeMonomial wordRow13.powers x y z b*
          v (gridIndex 210 (by decide) wordRow13.target) := by
  norm_num [source13,gridIndex,wordRow13,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link13
theorem word_link61 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source61 x y z b v=
      v (gridIndex 210 (by decide) wordRow61.source)-
        (-1:ℂ)^wordRow61.count*fourPrimeMonomial wordRow61.powers x y z b*
          v (gridIndex 210 (by decide) wordRow61.target) := by
  norm_num [source61,gridIndex,wordRow61,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link61
theorem word_link62 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source62 x y z b v=
      v (gridIndex 210 (by decide) wordRow62.source)-
        (-1:ℂ)^wordRow62.count*fourPrimeMonomial wordRow62.powers x y z b*
          v (gridIndex 210 (by decide) wordRow62.target) := by
  norm_num [source62,gridIndex,wordRow62,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link62
theorem word_link123 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source123 x y z b v=
      v (gridIndex 210 (by decide) wordRow123.source)-
        (-1:ℂ)^wordRow123.count*fourPrimeMonomial wordRow123.powers x y z b*
          v (gridIndex 210 (by decide) wordRow123.target) := by
  norm_num [source123,gridIndex,wordRow123,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link123
theorem word_link124 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source124 x y z b v=
      v (gridIndex 210 (by decide) wordRow124.source)-
        (-1:ℂ)^wordRow124.count*fourPrimeMonomial wordRow124.powers x y z b*
          v (gridIndex 210 (by decide) wordRow124.target) := by
  norm_num [source124,gridIndex,wordRow124,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link124
theorem word_link1 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1 x y z b v=
      v (gridIndex 210 (by decide) wordRow1.source)-
        (-1:ℂ)^wordRow1.count*fourPrimeMonomial wordRow1.powers x y z b*
          v (gridIndex 210 (by decide) wordRow1.target) := by
  norm_num [source1,gridIndex,wordRow1,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link1
theorem word_link9 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source9 x y z b v=
      v (gridIndex 210 (by decide) wordRow9.source)-
        (-1:ℂ)^wordRow9.count*fourPrimeMonomial wordRow9.powers x y z b*
          v (gridIndex 210 (by decide) wordRow9.target) := by
  norm_num [source9,gridIndex,wordRow9,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link9
theorem word_link17 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source17 x y z b v=
      v (gridIndex 210 (by decide) wordRow17.source)-
        (-1:ℂ)^wordRow17.count*fourPrimeMonomial wordRow17.powers x y z b*
          v (gridIndex 210 (by decide) wordRow17.target) := by
  norm_num [source17,gridIndex,wordRow17,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link17
theorem word_link30 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source30 x y z b v=
      v (gridIndex 210 (by decide) wordRow30.source)-
        (-1:ℂ)^wordRow30.count*fourPrimeMonomial wordRow30.powers x y z b*
          v (gridIndex 210 (by decide) wordRow30.target) := by
  norm_num [source30,gridIndex,wordRow30,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link30
theorem word_link128 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source128 x y z b v=
      v (gridIndex 210 (by decide) wordRow128.source)-
        (-1:ℂ)^wordRow128.count*fourPrimeMonomial wordRow128.powers x y z b*
          v (gridIndex 210 (by decide) wordRow128.target) := by
  norm_num [source128,gridIndex,wordRow128,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link128

theorem word_link18 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source18 x y z b v=
      v (gridIndex 210 (by decide) wordRow18.source)-
        (-1:ℂ)^wordRow18.count*fourPrimeMonomial wordRow18.powers x y z b*
          v (gridIndex 210 (by decide) wordRow18.target) := by
  norm_num [source18,gridIndex,wordRow18,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link18
theorem word_link79 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source79 x y z b v=
      v (gridIndex 210 (by decide) wordRow79.source)-
        (-1:ℂ)^wordRow79.count*fourPrimeMonomial wordRow79.powers x y z b*
          v (gridIndex 210 (by decide) wordRow79.target) := by
  norm_num [source79,gridIndex,wordRow79,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link79
theorem word_link130 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source130 x y z b v=
      v (gridIndex 210 (by decide) wordRow130.source)-
        (-1:ℂ)^wordRow130.count*fourPrimeMonomial wordRow130.powers x y z b*
          v (gridIndex 210 (by decide) wordRow130.target) := by
  norm_num [source130,gridIndex,wordRow130,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link130
theorem word_link29 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source29 x y z b v=
      v (gridIndex 210 (by decide) wordRow29.source)-
        (-1:ℂ)^wordRow29.count*fourPrimeMonomial wordRow29.powers x y z b*
          v (gridIndex 210 (by decide) wordRow29.target) := by
  norm_num [source29,gridIndex,wordRow29,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link29
theorem word_link71 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source71 x y z b v=
      v (gridIndex 210 (by decide) wordRow71.source)-
        (-1:ℂ)^wordRow71.count*fourPrimeMonomial wordRow71.powers x y z b*
          v (gridIndex 210 (by decide) wordRow71.target) := by
  norm_num [source71,gridIndex,wordRow71,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link71
theorem word_link138 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source138 x y z b v=
      v (gridIndex 210 (by decide) wordRow138.source)-
        (-1:ℂ)^wordRow138.count*fourPrimeMonomial wordRow138.powers x y z b*
          v (gridIndex 210 (by decide) wordRow138.target) := by
  norm_num [source138,gridIndex,wordRow138,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link138
theorem word_link174 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source174 x y z b v=
      v (gridIndex 210 (by decide) wordRow174.source)-
        (-1:ℂ)^wordRow174.count*fourPrimeMonomial wordRow174.powers x y z b*
          v (gridIndex 210 (by decide) wordRow174.target) := by
  norm_num [source174,gridIndex,wordRow174,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link174
theorem word_link16 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source16 x y z b v=
      v (gridIndex 210 (by decide) wordRow16.source)-
        (-1:ℂ)^wordRow16.count*fourPrimeMonomial wordRow16.powers x y z b*
          v (gridIndex 210 (by decide) wordRow16.target) := by
  norm_num [source16,gridIndex,wordRow16,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link16
theorem word_link11 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source11 x y z b v=
      v (gridIndex 210 (by decide) wordRow11.source)-
        (-1:ℂ)^wordRow11.count*fourPrimeMonomial wordRow11.powers x y z b*
          v (gridIndex 210 (by decide) wordRow11.target) := by
  norm_num [source11,gridIndex,wordRow11,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link11
theorem word_link26 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source26 x y z b v=
      v (gridIndex 210 (by decide) wordRow26.source)-
        (-1:ℂ)^wordRow26.count*fourPrimeMonomial wordRow26.powers x y z b*
          v (gridIndex 210 (by decide) wordRow26.target) := by
  norm_num [source26,gridIndex,wordRow26,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link26
theorem word_link60 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source60 x y z b v=
      v (gridIndex 210 (by decide) wordRow60.source)-
        (-1:ℂ)^wordRow60.count*fourPrimeMonomial wordRow60.powers x y z b*
          v (gridIndex 210 (by decide) wordRow60.target) := by
  norm_num [source60,gridIndex,wordRow60,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link60
theorem word_link122 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source122 x y z b v=
      v (gridIndex 210 (by decide) wordRow122.source)-
        (-1:ℂ)^wordRow122.count*fourPrimeMonomial wordRow122.powers x y z b*
          v (gridIndex 210 (by decide) wordRow122.target) := by
  norm_num [source122,gridIndex,wordRow122,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link122
theorem word_link152 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source152 x y z b v=
      v (gridIndex 210 (by decide) wordRow152.source)-
        (-1:ℂ)^wordRow152.count*fourPrimeMonomial wordRow152.powers x y z b*
          v (gridIndex 210 (by decide) wordRow152.target) := by
  norm_num [source152,gridIndex,wordRow152,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link152
theorem word_link12 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source12 x y z b v=
      v (gridIndex 210 (by decide) wordRow12.source)-
        (-1:ℂ)^wordRow12.count*fourPrimeMonomial wordRow12.powers x y z b*
          v (gridIndex 210 (by decide) wordRow12.target) := by
  norm_num [source12,gridIndex,wordRow12,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link12
theorem word_link67 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source67 x y z b v=
      v (gridIndex 210 (by decide) wordRow67.source)-
        (-1:ℂ)^wordRow67.count*fourPrimeMonomial wordRow67.powers x y z b*
          v (gridIndex 210 (by decide) wordRow67.target) := by
  norm_num [source67,gridIndex,wordRow67,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link67

theorem word_link163 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source163 x y z b v=
      v (gridIndex 210 (by decide) wordRow163.source)-
        (-1:ℂ)^wordRow163.count*fourPrimeMonomial wordRow163.powers x y z b*
          v (gridIndex 210 (by decide) wordRow163.target) := by
  norm_num [source163,gridIndex,wordRow163,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link163
theorem word_link164 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source164 x y z b v=
      v (gridIndex 210 (by decide) wordRow164.source)-
        (-1:ℂ)^wordRow164.count*fourPrimeMonomial wordRow164.powers x y z b*
          v (gridIndex 210 (by decide) wordRow164.target) := by
  norm_num [source164,gridIndex,wordRow164,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link164
theorem word_link4 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source4 x y z b v=
      v (gridIndex 210 (by decide) wordRow4.source)-
        (-1:ℂ)^wordRow4.count*fourPrimeMonomial wordRow4.powers x y z b*
          v (gridIndex 210 (by decide) wordRow4.target) := by
  norm_num [source4,gridIndex,wordRow4,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link4
theorem word_link8 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source8 x y z b v=
      v (gridIndex 210 (by decide) wordRow8.source)-
        (-1:ℂ)^wordRow8.count*fourPrimeMonomial wordRow8.powers x y z b*
          v (gridIndex 210 (by decide) wordRow8.target) := by
  norm_num [source8,gridIndex,wordRow8,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link8
theorem word_link21 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source21 x y z b v=
      v (gridIndex 210 (by decide) wordRow21.source)-
        (-1:ℂ)^wordRow21.count*fourPrimeMonomial wordRow21.powers x y z b*
          v (gridIndex 210 (by decide) wordRow21.target) := by
  norm_num [source21,gridIndex,wordRow21,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link21
theorem word_link31 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source31 x y z b v=
      v (gridIndex 210 (by decide) wordRow31.source)-
        (-1:ℂ)^wordRow31.count*fourPrimeMonomial wordRow31.powers x y z b*
          v (gridIndex 210 (by decide) wordRow31.target) := by
  norm_num [source31,gridIndex,wordRow31,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link31
theorem word_link127 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source127 x y z b v=
      v (gridIndex 210 (by decide) wordRow127.source)-
        (-1:ℂ)^wordRow127.count*fourPrimeMonomial wordRow127.powers x y z b*
          v (gridIndex 210 (by decide) wordRow127.target) := by
  norm_num [source127,gridIndex,wordRow127,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link127
theorem word_link129 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source129 x y z b v=
      v (gridIndex 210 (by decide) wordRow129.source)-
        (-1:ℂ)^wordRow129.count*fourPrimeMonomial wordRow129.powers x y z b*
          v (gridIndex 210 (by decide) wordRow129.target) := by
  norm_num [source129,gridIndex,wordRow129,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link129
theorem word_link3 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source3 x y z b v=
      v (gridIndex 210 (by decide) wordRow3.source)-
        (-1:ℂ)^wordRow3.count*fourPrimeMonomial wordRow3.powers x y z b*
          v (gridIndex 210 (by decide) wordRow3.target) := by
  norm_num [source3,gridIndex,wordRow3,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link3
theorem word_link104 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source104 x y z b v=
      v (gridIndex 210 (by decide) wordRow104.source)-
        (-1:ℂ)^wordRow104.count*fourPrimeMonomial wordRow104.powers x y z b*
          v (gridIndex 210 (by decide) wordRow104.target) := by
  norm_num [source104,gridIndex,wordRow104,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link104
theorem word_link148 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source148 x y z b v=
      v (gridIndex 210 (by decide) wordRow148.source)-
        (-1:ℂ)^wordRow148.count*fourPrimeMonomial wordRow148.powers x y z b*
          v (gridIndex 210 (by decide) wordRow148.target) := by
  norm_num [source148,gridIndex,wordRow148,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link148
theorem word_link149 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source149 x y z b v=
      v (gridIndex 210 (by decide) wordRow149.source)-
        (-1:ℂ)^wordRow149.count*fourPrimeMonomial wordRow149.powers x y z b*
          v (gridIndex 210 (by decide) wordRow149.target) := by
  norm_num [source149,gridIndex,wordRow149,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link149
theorem word_link103 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source103 x y z b v=
      v (gridIndex 210 (by decide) wordRow103.source)-
        (-1:ℂ)^wordRow103.count*fourPrimeMonomial wordRow103.powers x y z b*
          v (gridIndex 210 (by decide) wordRow103.target) := by
  norm_num [source103,gridIndex,wordRow103,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link103
theorem word_link161 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source161 x y z b v=
      v (gridIndex 210 (by decide) wordRow161.source)-
        (-1:ℂ)^wordRow161.count*fourPrimeMonomial wordRow161.powers x y z b*
          v (gridIndex 210 (by decide) wordRow161.target) := by
  norm_num [source161,gridIndex,wordRow161,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link161
theorem word_link179 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source179 x y z b v=
      v (gridIndex 210 (by decide) wordRow179.source)-
        (-1:ℂ)^wordRow179.count*fourPrimeMonomial wordRow179.powers x y z b*
          v (gridIndex 210 (by decide) wordRow179.target) := by
  norm_num [source179,gridIndex,wordRow179,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link179

theorem word_link68 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source68 x y z b v=
      v (gridIndex 210 (by decide) wordRow68.source)-
        (-1:ℂ)^wordRow68.count*fourPrimeMonomial wordRow68.powers x y z b*
          v (gridIndex 210 (by decide) wordRow68.target) := by
  norm_num [source68,gridIndex,wordRow68,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link68
theorem word_link126 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source126 x y z b v=
      v (gridIndex 210 (by decide) wordRow126.source)-
        (-1:ℂ)^wordRow126.count*fourPrimeMonomial wordRow126.powers x y z b*
          v (gridIndex 210 (by decide) wordRow126.target) := by
  norm_num [source126,gridIndex,wordRow126,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link126
theorem word_link136 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source136 x y z b v=
      v (gridIndex 210 (by decide) wordRow136.source)-
        (-1:ℂ)^wordRow136.count*fourPrimeMonomial wordRow136.powers x y z b*
          v (gridIndex 210 (by decide) wordRow136.target) := by
  norm_num [source136,gridIndex,wordRow136,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link136
theorem word_link14 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source14 x y z b v=
      v (gridIndex 210 (by decide) wordRow14.source)-
        (-1:ℂ)^wordRow14.count*fourPrimeMonomial wordRow14.powers x y z b*
          v (gridIndex 210 (by decide) wordRow14.target) := by
  norm_num [source14,gridIndex,wordRow14,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link14
theorem word_link22 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source22 x y z b v=
      v (gridIndex 210 (by decide) wordRow22.source)-
        (-1:ℂ)^wordRow22.count*fourPrimeMonomial wordRow22.powers x y z b*
          v (gridIndex 210 (by decide) wordRow22.target) := by
  norm_num [source22,gridIndex,wordRow22,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link22
theorem word_link32 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source32 x y z b v=
      v (gridIndex 210 (by decide) wordRow32.source)-
        (-1:ℂ)^wordRow32.count*fourPrimeMonomial wordRow32.powers x y z b*
          v (gridIndex 210 (by decide) wordRow32.target) := by
  norm_num [source32,gridIndex,wordRow32,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link32
theorem word_link173 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source173 x y z b v=
      v (gridIndex 210 (by decide) wordRow173.source)-
        (-1:ℂ)^wordRow173.count*fourPrimeMonomial wordRow173.powers x y z b*
          v (gridIndex 210 (by decide) wordRow173.target) := by
  norm_num [source173,gridIndex,wordRow173,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link173
theorem word_link146 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source146 x y z b v=
      v (gridIndex 210 (by decide) wordRow146.source)-
        (-1:ℂ)^wordRow146.count*fourPrimeMonomial wordRow146.powers x y z b*
          v (gridIndex 210 (by decide) wordRow146.target) := by
  norm_num [source146,gridIndex,wordRow146,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link146
theorem word_link159 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source159 x y z b v=
      v (gridIndex 210 (by decide) wordRow159.source)-
        (-1:ℂ)^wordRow159.count*fourPrimeMonomial wordRow159.powers x y z b*
          v (gridIndex 210 (by decide) wordRow159.target) := by
  norm_num [source159,gridIndex,wordRow159,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link159
theorem word_link19 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source19 x y z b v=
      v (gridIndex 210 (by decide) wordRow19.source)-
        (-1:ℂ)^wordRow19.count*fourPrimeMonomial wordRow19.powers x y z b*
          v (gridIndex 210 (by decide) wordRow19.target) := by
  norm_num [source19,gridIndex,wordRow19,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link19
theorem word_link23 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source23 x y z b v=
      v (gridIndex 210 (by decide) wordRow23.source)-
        (-1:ℂ)^wordRow23.count*fourPrimeMonomial wordRow23.powers x y z b*
          v (gridIndex 210 (by decide) wordRow23.target) := by
  norm_num [source23,gridIndex,wordRow23,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link23
theorem word_link155 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source155 x y z b v=
      v (gridIndex 210 (by decide) wordRow155.source)-
        (-1:ℂ)^wordRow155.count*fourPrimeMonomial wordRow155.powers x y z b*
          v (gridIndex 210 (by decide) wordRow155.target) := by
  norm_num [source155,gridIndex,wordRow155,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link155
theorem word_link150 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source150 x y z b v=
      v (gridIndex 210 (by decide) wordRow150.source)-
        (-1:ℂ)^wordRow150.count*fourPrimeMonomial wordRow150.powers x y z b*
          v (gridIndex 210 (by decide) wordRow150.target) := by
  norm_num [source150,gridIndex,wordRow150,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link150
theorem word_link25 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source25 x y z b v=
      v (gridIndex 210 (by decide) wordRow25.source)-
        (-1:ℂ)^wordRow25.count*fourPrimeMonomial wordRow25.powers x y z b*
          v (gridIndex 210 (by decide) wordRow25.target) := by
  norm_num [source25,gridIndex,wordRow25,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link25
theorem word_link15 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source15 x y z b v=
      v (gridIndex 210 (by decide) wordRow15.source)-
        (-1:ℂ)^wordRow15.count*fourPrimeMonomial wordRow15.powers x y z b*
          v (gridIndex 210 (by decide) wordRow15.target) := by
  norm_num [source15,gridIndex,wordRow15,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link15

theorem word_link33 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source33 x y z b v=
      v (gridIndex 210 (by decide) wordRow33.source)-
        (-1:ℂ)^wordRow33.count*fourPrimeMonomial wordRow33.powers x y z b*
          v (gridIndex 210 (by decide) wordRow33.target) := by
  norm_num [source33,gridIndex,wordRow33,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link33
theorem word_link139 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source139 x y z b v=
      v (gridIndex 210 (by decide) wordRow139.source)-
        (-1:ℂ)^wordRow139.count*fourPrimeMonomial wordRow139.powers x y z b*
          v (gridIndex 210 (by decide) wordRow139.target) := by
  norm_num [source139,gridIndex,wordRow139,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link139
theorem word_link153 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source153 x y z b v=
      v (gridIndex 210 (by decide) wordRow153.source)-
        (-1:ℂ)^wordRow153.count*fourPrimeMonomial wordRow153.powers x y z b*
          v (gridIndex 210 (by decide) wordRow153.target) := by
  norm_num [source153,gridIndex,wordRow153,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link153
theorem word_link28 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source28 x y z b v=
      v (gridIndex 210 (by decide) wordRow28.source)-
        (-1:ℂ)^wordRow28.count*fourPrimeMonomial wordRow28.powers x y z b*
          v (gridIndex 210 (by decide) wordRow28.target) := by
  norm_num [source28,gridIndex,wordRow28,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link28
theorem word_link166 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source166 x y z b v=
      v (gridIndex 210 (by decide) wordRow166.source)-
        (-1:ℂ)^wordRow166.count*fourPrimeMonomial wordRow166.powers x y z b*
          v (gridIndex 210 (by decide) wordRow166.target) := by
  norm_num [source166,gridIndex,wordRow166,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link166
theorem word_link24 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source24 x y z b v=
      v (gridIndex 210 (by decide) wordRow24.source)-
        (-1:ℂ)^wordRow24.count*fourPrimeMonomial wordRow24.powers x y z b*
          v (gridIndex 210 (by decide) wordRow24.target) := by
  norm_num [source24,gridIndex,wordRow24,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link24
theorem word_link157 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source157 x y z b v=
      v (gridIndex 210 (by decide) wordRow157.source)-
        (-1:ℂ)^wordRow157.count*fourPrimeMonomial wordRow157.powers x y z b*
          v (gridIndex 210 (by decide) wordRow157.target) := by
  norm_num [source157,gridIndex,wordRow157,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link157
theorem word_link162 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source162 x y z b v=
      v (gridIndex 210 (by decide) wordRow162.source)-
        (-1:ℂ)^wordRow162.count*fourPrimeMonomial wordRow162.powers x y z b*
          v (gridIndex 210 (by decide) wordRow162.target) := by
  norm_num [source162,gridIndex,wordRow162,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link162
theorem word_link27 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source27 x y z b v=
      v (gridIndex 210 (by decide) wordRow27.source)-
        (-1:ℂ)^wordRow27.count*fourPrimeMonomial wordRow27.powers x y z b*
          v (gridIndex 210 (by decide) wordRow27.target) := by
  norm_num [source27,gridIndex,wordRow27,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link27
theorem word_link158 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source158 x y z b v=
      v (gridIndex 210 (by decide) wordRow158.source)-
        (-1:ℂ)^wordRow158.count*fourPrimeMonomial wordRow158.powers x y z b*
          v (gridIndex 210 (by decide) wordRow158.target) := by
  norm_num [source158,gridIndex,wordRow158,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link158
theorem word_link20 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source20 x y z b v=
      v (gridIndex 210 (by decide) wordRow20.source)-
        (-1:ℂ)^wordRow20.count*fourPrimeMonomial wordRow20.powers x y z b*
          v (gridIndex 210 (by decide) wordRow20.target) := by
  norm_num [source20,gridIndex,wordRow20,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link20
theorem word_link154 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source154 x y z b v=
      v (gridIndex 210 (by decide) wordRow154.source)-
        (-1:ℂ)^wordRow154.count*fourPrimeMonomial wordRow154.powers x y z b*
          v (gridIndex 210 (by decide) wordRow154.target) := by
  norm_num [source154,gridIndex,wordRow154,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link154
theorem word_link172 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source172 x y z b v=
      v (gridIndex 210 (by decide) wordRow172.source)-
        (-1:ℂ)^wordRow172.count*fourPrimeMonomial wordRow172.powers x y z b*
          v (gridIndex 210 (by decide) wordRow172.target) := by
  norm_num [source172,gridIndex,wordRow172,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link172
theorem word_link140 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source140 x y z b v=
      v (gridIndex 210 (by decide) wordRow140.source)-
        (-1:ℂ)^wordRow140.count*fourPrimeMonomial wordRow140.powers x y z b*
          v (gridIndex 210 (by decide) wordRow140.target) := by
  norm_num [source140,gridIndex,wordRow140,fourPrimeMonomial]
  <;> field_simp [hx,hy,hz,hb] <;> ring_nf <;> simp

#print axioms word_link140

end SmallLevelTwentyOneLargeGridLinks
end
end

/-! ## SmallLevelTwentyOneLargeGridActualLinksBundleV4 -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyOneLargeGridLinks
open Complex SmallLevelTwentyOneFiniteGrid SmallLevelTwentyOneLargeGridAlgebra
open SmallLevelTwentyOneLargeGridData SmallLevelTwentyOneLargeGridModel SmallLevelTwentyOneKnownWords

theorem actual_link000 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 0) 1 f ε s v=source5 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link5 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v).symm
#print axioms actual_link000

theorem actual_link001 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 1) 1 f ε s v=source0 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow0.source)-
    coefficient wordRow0 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow0.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link0 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link001

theorem actual_link002 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 2) 1 f ε s v=source2 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow2.source)-
    coefficient wordRow2 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow2.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link2 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link002

theorem actual_link003 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 3) 1 f ε s v=source6 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow6.source)-
    coefficient wordRow6 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow6.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link6 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link003

theorem actual_link004 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 4) 1 f ε s v=source7 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow7.source)-
    coefficient wordRow7 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow7.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link7 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link004

theorem actual_link005 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 5) 1 f ε s v=source10 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow10.source)-
    coefficient wordRow10 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow10.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link10 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link005

theorem actual_link006 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 6) 1 f ε s v=source13 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow13.source)-
    coefficient wordRow13 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow13.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link13 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link006

theorem actual_link007 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 7) 1 f ε s v=source61 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow61.source)-
    coefficient wordRow61 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow61.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link61 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link007

theorem actual_link008 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 8) 1 f ε s v=source62 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow62.source)-
    coefficient wordRow62 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow62.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link62 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link008

theorem actual_link009 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 9) 1 f ε s v=source123 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow123.source)-
    coefficient wordRow123 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow123.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link123 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link009

theorem actual_link010 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 10) 1 f ε s v=source124 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow124.source)-
    coefficient wordRow124 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow124.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link124 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link010

theorem actual_link011 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 11) 1 f ε s v=source1 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow1.source)-
    coefficient wordRow1 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow1.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link1 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link011

theorem actual_link012 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 12) 1 f ε s v=source9 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow9.source)-
    coefficient wordRow9 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow9.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link9 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link012

theorem actual_link013 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 13) 1 f ε s v=source17 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow17.source)-
    coefficient wordRow17 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow17.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link17 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link013

theorem actual_link014 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 14) 1 f ε s v=source30 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow30.source)-
    coefficient wordRow30 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow30.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link30 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link014

theorem actual_link015 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 15) 1 f ε s v=source125 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link125 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v).symm
#print axioms actual_link015

theorem actual_link016 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 16) 1 f ε s v=source128 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow128.source)-
    coefficient wordRow128 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow128.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link128 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link016

theorem actual_link017 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 17) 1 f ε s v=source18 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow18.source)-
    coefficient wordRow18 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow18.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link18 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link017

theorem actual_link018 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 18) 1 f ε s v=source79 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow79.source)-
    coefficient wordRow79 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow79.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link79 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link018

theorem actual_link019 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 19) 1 f ε s v=source130 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow130.source)-
    coefficient wordRow130 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow130.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link130 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link019

theorem actual_link020 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 20) 1 f ε s v=source29 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow29.source)-
    coefficient wordRow29 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow29.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link29 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link020

theorem actual_link021 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 21) 1 f ε s v=source71 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow71.source)-
    coefficient wordRow71 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow71.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link71 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link021

theorem actual_link022 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 22) 1 f ε s v=source138 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow138.source)-
    coefficient wordRow138 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow138.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link138 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link022

theorem actual_link023 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 23) 1 f ε s v=source174 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow174.source)-
    coefficient wordRow174 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow174.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link174 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link023

theorem actual_link024 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 24) 1 f ε s v=source1451 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1451 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v).symm
#print axioms actual_link024

theorem actual_link025 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 25) 1 f ε s v=source16 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow16.source)-
    coefficient wordRow16 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow16.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link16 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link025

theorem actual_link026 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 26) 1 f ε s v=source11 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow11.source)-
    coefficient wordRow11 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow11.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link11 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link026

theorem actual_link027 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 27) 1 f ε s v=source26 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow26.source)-
    coefficient wordRow26 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow26.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link26 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link027

theorem actual_link028 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 28) 1 f ε s v=source60 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow60.source)-
    coefficient wordRow60 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow60.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link60 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link028

theorem actual_link029 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 29) 1 f ε s v=source122 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow122.source)-
    coefficient wordRow122 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow122.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link122 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link029

theorem actual_link030 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 30) 1 f ε s v=source152 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow152.source)-
    coefficient wordRow152 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow152.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link152 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link030

theorem actual_link031 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 31) 1 f ε s v=source12 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow12.source)-
    coefficient wordRow12 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow12.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link12 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link031

theorem actual_link032 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 32) 1 f ε s v=source67 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow67.source)-
    coefficient wordRow67 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow67.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link67 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link032

theorem actual_link033 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 33) 1 f ε s v=source163 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow163.source)-
    coefficient wordRow163 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow163.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link163 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link033

theorem actual_link034 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 34) 1 f ε s v=source164 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow164.source)-
    coefficient wordRow164 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow164.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link164 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link034

theorem actual_link035 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 35) 1 f ε s v=source1037 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1037 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v).symm
#print axioms actual_link035

theorem actual_link036 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 36) 1 f ε s v=source4 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow4.source)-
    coefficient wordRow4 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow4.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link4 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link036

theorem actual_link037 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 37) 1 f ε s v=source8 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow8.source)-
    coefficient wordRow8 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow8.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link8 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link037

theorem actual_link038 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 38) 1 f ε s v=source21 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow21.source)-
    coefficient wordRow21 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow21.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link21 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link038

theorem actual_link039 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 39) 1 f ε s v=source31 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow31.source)-
    coefficient wordRow31 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow31.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link31 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link039

theorem actual_link040 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 40) 1 f ε s v=source127 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow127.source)-
    coefficient wordRow127 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow127.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link127 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link040

theorem actual_link041 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 41) 1 f ε s v=source129 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow129.source)-
    coefficient wordRow129 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow129.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link129 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link041

theorem actual_link042 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 42) 1 f ε s v=source3 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow3.source)-
    coefficient wordRow3 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow3.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link3 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link042

theorem actual_link043 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 43) 1 f ε s v=source104 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow104.source)-
    coefficient wordRow104 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow104.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link104 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link043

theorem actual_link044 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 44) 1 f ε s v=source148 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow148.source)-
    coefficient wordRow148 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow148.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link148 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link044

theorem actual_link045 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 45) 1 f ε s v=source149 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow149.source)-
    coefficient wordRow149 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow149.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link149 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link045

theorem actual_link046 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 46) 1 f ε s v=source1102 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1102.q taylorRow1102.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1102.q taylorRow1102.source 0 s*
      sampleSum 210 (by decide) taylorRow1102.q taylorRow1102.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1102 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link046

theorem actual_link047 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 47) 1 f ε s v=source103 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow103.source)-
    coefficient wordRow103 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow103.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link103 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link047

theorem actual_link048 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 48) 1 f ε s v=source161 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow161.source)-
    coefficient wordRow161 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow161.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link161 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link048

theorem actual_link049 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 49) 1 f ε s v=source179 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow179.source)-
    coefficient wordRow179 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow179.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link179 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link049

theorem actual_link050 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 50) 1 f ε s v=source1103 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1103.q taylorRow1103.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1103.q taylorRow1103.source 0 s*
      sampleSum 210 (by decide) taylorRow1103.q taylorRow1103.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1103 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link050

theorem actual_link051 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 51) 1 f ε s v=source68 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow68.source)-
    coefficient wordRow68 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow68.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link68 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link051

theorem actual_link052 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 52) 1 f ε s v=source126 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow126.source)-
    coefficient wordRow126 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow126.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link126 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link052

theorem actual_link053 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 53) 1 f ε s v=source136 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow136.source)-
    coefficient wordRow136 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow136.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link136 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link053

theorem actual_link054 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 54) 1 f ε s v=source1246 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1246 f ha hu hv s v).symm
#print axioms actual_link054

theorem actual_link055 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 55) 1 f ε s v=source14 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow14.source)-
    coefficient wordRow14 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow14.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link14 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link055

theorem actual_link056 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 56) 1 f ε s v=source22 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow22.source)-
    coefficient wordRow22 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow22.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link22 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link056

theorem actual_link057 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 57) 1 f ε s v=source32 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow32.source)-
    coefficient wordRow32 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow32.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link32 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link057

theorem actual_link058 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 58) 1 f ε s v=source173 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow173.source)-
    coefficient wordRow173 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow173.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link173 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link058

theorem actual_link059 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 59) 1 f ε s v=source1048 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1048.q taylorRow1048.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1048.q taylorRow1048.source 0 s*
      sampleSum 210 (by decide) taylorRow1048.q taylorRow1048.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1048 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link059

theorem actual_link060 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 60) 1 f ε s v=source146 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow146.source)-
    coefficient wordRow146 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow146.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link146 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link060

theorem actual_link061 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 61) 1 f ε s v=source159 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow159.source)-
    coefficient wordRow159 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow159.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link159 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link061

theorem actual_link062 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 62) 1 f ε s v=source19 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow19.source)-
    coefficient wordRow19 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow19.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link19 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link062

theorem actual_link063 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 63) 1 f ε s v=source1051 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1051.q taylorRow1051.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1051.q taylorRow1051.source 0 s*
      sampleSum 210 (by decide) taylorRow1051.q taylorRow1051.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1051 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link063

theorem actual_link064 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 64) 1 f ε s v=source1052 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1052.q taylorRow1052.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1052.q taylorRow1052.source 0 s*
      sampleSum 210 (by decide) taylorRow1052.q taylorRow1052.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1052 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link064

theorem actual_link065 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 65) 1 f ε s v=source23 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow23.source)-
    coefficient wordRow23 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow23.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link23 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link065

theorem actual_link066 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 66) 1 f ε s v=source155 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow155.source)-
    coefficient wordRow155 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow155.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link155 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link066

theorem actual_link067 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 67) 1 f ε s v=source1054 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1054.q taylorRow1054.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1054.q taylorRow1054.source 0 s*
      sampleSum 210 (by decide) taylorRow1054.q taylorRow1054.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1054 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link067

theorem actual_link068 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 68) 1 f ε s v=source150 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow150.source)-
    coefficient wordRow150 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow150.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link150 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link068

theorem actual_link069 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 69) 1 f ε s v=source1099 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1099 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v).symm
#print axioms actual_link069

theorem actual_link070 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 70) 1 f ε s v=source25 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow25.source)-
    coefficient wordRow25 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow25.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link25 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link070

theorem actual_link071 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 71) 1 f ε s v=source15 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow15.source)-
    coefficient wordRow15 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow15.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link15 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link071

theorem actual_link072 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 72) 1 f ε s v=source33 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow33.source)-
    coefficient wordRow33 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow33.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link33 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link072

theorem actual_link073 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 73) 1 f ε s v=source139 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow139.source)-
    coefficient wordRow139 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow139.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link139 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link073

theorem actual_link074 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 74) 1 f ε s v=source1049 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1049.q taylorRow1049.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1049.q taylorRow1049.source 0 s*
      sampleSum 210 (by decide) taylorRow1049.q taylorRow1049.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1049 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link074

theorem actual_link075 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 75) 1 f ε s v=source153 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow153.source)-
    coefficient wordRow153 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow153.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link153 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link075

theorem actual_link076 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 76) 1 f ε s v=source28 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow28.source)-
    coefficient wordRow28 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow28.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link28 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link076

theorem actual_link077 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 77) 1 f ε s v=source166 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow166.source)-
    coefficient wordRow166 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow166.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link166 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link077

theorem actual_link078 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 78) 1 f ε s v=source1050 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1050.q taylorRow1050.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1050.q taylorRow1050.source 0 s*
      sampleSum 210 (by decide) taylorRow1050.q taylorRow1050.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1050 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link078

theorem actual_link079 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 79) 1 f ε s v=source1053 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1053.q taylorRow1053.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1053.q taylorRow1053.source 0 s*
      sampleSum 210 (by decide) taylorRow1053.q taylorRow1053.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1053 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link079

theorem actual_link080 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 80) 1 f ε s v=source24 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow24.source)-
    coefficient wordRow24 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow24.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link24 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link080

theorem actual_link081 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 81) 1 f ε s v=source157 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow157.source)-
    coefficient wordRow157 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow157.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link157 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link081

theorem actual_link082 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 82) 1 f ε s v=source1055 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1055.q taylorRow1055.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1055.q taylorRow1055.source 0 s*
      sampleSum 210 (by decide) taylorRow1055.q taylorRow1055.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1055 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link082

theorem actual_link083 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 83) 1 f ε s v=source162 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow162.source)-
    coefficient wordRow162 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow162.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link162 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link083

theorem actual_link084 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 84) 1 f ε s v=source1104 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1104.q taylorRow1104.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1104.q taylorRow1104.source 0 s*
      sampleSum 210 (by decide) taylorRow1104.q taylorRow1104.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1104 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link084

theorem actual_link085 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 85) 1 f ε s v=source27 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow27.source)-
    coefficient wordRow27 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow27.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link27 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link085

theorem actual_link086 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 86) 1 f ε s v=source158 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow158.source)-
    coefficient wordRow158 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow158.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link158 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link086

theorem actual_link087 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 87) 1 f ε s v=source1044 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1044.q taylorRow1044.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1044.q taylorRow1044.source 0 s*
      sampleSum 210 (by decide) taylorRow1044.q taylorRow1044.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1044 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link087

theorem actual_link088 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 88) 1 f ε s v=source1105 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1105.q taylorRow1105.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1105.q taylorRow1105.source 0 s*
      sampleSum 210 (by decide) taylorRow1105.q taylorRow1105.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1105 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link088

theorem actual_link089 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 89) 1 f ε s v=source20 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow20.source)-
    coefficient wordRow20 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow20.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link20 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link089

theorem actual_link090 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 90) 1 f ε s v=source154 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow154.source)-
    coefficient wordRow154 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow154.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link154 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link090

theorem actual_link091 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 91) 1 f ε s v=source1045 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1045.q taylorRow1045.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1045.q taylorRow1045.source 0 s*
      sampleSum 210 (by decide) taylorRow1045.q taylorRow1045.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1045 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link091

theorem actual_link092 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 92) 1 f ε s v=source1152 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1152.q taylorRow1152.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1152.q taylorRow1152.source 0 s*
      sampleSum 210 (by decide) taylorRow1152.q taylorRow1152.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1152 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link092

theorem actual_link093 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 93) 1 f ε s v=source1043 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1043.q taylorRow1043.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1043.q taylorRow1043.source 0 s*
      sampleSum 210 (by decide) taylorRow1043.q taylorRow1043.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1043 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link093

theorem actual_link094 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 94) 1 f ε s v=source1153 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1153.q taylorRow1153.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1153.q taylorRow1153.source 0 s*
      sampleSum 210 (by decide) taylorRow1153.q taylorRow1153.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1153 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link094

theorem actual_link095 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 95) 1 f ε s v=source1042 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1042.q taylorRow1042.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1042.q taylorRow1042.source 0 s*
      sampleSum 210 (by decide) taylorRow1042.q taylorRow1042.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1042 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link095

theorem actual_link096 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 96) 1 f ε s v=source1247 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1247 f ha hu hv s v).symm
#print axioms actual_link096

theorem actual_link097 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 97) 1 f ε s v=source172 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow172.source)-
    coefficient wordRow172 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow172.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link172 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link097

theorem actual_link098 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 98) 1 f ε s v=source1121 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1121.q taylorRow1121.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1121.q taylorRow1121.source 0 s*
      sampleSum 210 (by decide) taylorRow1121.q taylorRow1121.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1121 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link098

theorem actual_link099 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 99) 1 f ε s v=source1252 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1252 f ha hu hv s v).symm
#print axioms actual_link099

theorem actual_link100 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 100) 1 f ε s v=source1100 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1100.q taylorRow1100.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1100.q taylorRow1100.source 0 s*
      sampleSum 210 (by decide) taylorRow1100.q taylorRow1100.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1100 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link100

theorem actual_link101 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 101) 1 f ε s v=source1123 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1123.q taylorRow1123.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1123.q taylorRow1123.source 0 s*
      sampleSum 210 (by decide) taylorRow1123.q taylorRow1123.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1123 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link101

theorem actual_link102 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 102) 1 f ε s v=source1257 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1257 f ha hu hv s v).symm
#print axioms actual_link102

theorem actual_link103 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 103) 1 f ε s v=source1271 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1271 f ha hu hv s v).symm
#print axioms actual_link103

theorem actual_link104 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 104) 1 f ε s v=source1047 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1047.q taylorRow1047.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1047.q taylorRow1047.source 0 s*
      sampleSum 210 (by decide) taylorRow1047.q taylorRow1047.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1047 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link104

theorem actual_link105 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 105) 1 f ε s v=source1149 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1149 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v).symm
#print axioms actual_link105

theorem actual_link106 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 106) 1 f ε s v=source1046 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1046.q taylorRow1046.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1046.q taylorRow1046.source 0 s*
      sampleSum 210 (by decide) taylorRow1046.q taylorRow1046.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1046 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link106

theorem actual_link107 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 107) 1 f ε s v=source1292 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1292 f ha hu hv s v).symm
#print axioms actual_link107

theorem actual_link108 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 108) 1 f ε s v=source1294 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1294 f ha hu hv s v).symm
#print axioms actual_link108

theorem actual_link109 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 109) 1 f ε s v=source1298 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1298 f ha hu hv s v).symm
#print axioms actual_link109

theorem actual_link110 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 110) 1 f ε s v=source1122 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1122.q taylorRow1122.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1122.q taylorRow1122.source 0 s*
      sampleSum 210 (by decide) taylorRow1122.q taylorRow1122.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1122 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link110

theorem actual_link111 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 111) 1 f ε s v=source140 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change v (gridIndex 210 (by decide) wordRow140.source)-
    coefficient wordRow140 1 (ε*I^(2*1)) 0 s*
      v (gridIndex 210 (by decide) wordRow140.target)=_
  rw [coefficient_leading,show ε*I^(2*1)= -1 from hE]
  exact (word_link140 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link111

theorem actual_link112 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 112) 1 f ε s v=source1299 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1299 f ha hu hv s v).symm
#print axioms actual_link112

theorem actual_link113 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 113) 1 f ε s v=source1203 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1203 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v).symm
#print axioms actual_link113

theorem actual_link114 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 114) 1 f ε s v=source1085 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1085.q taylorRow1085.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1085.q taylorRow1085.source 0 s*
      sampleSum 210 (by decide) taylorRow1085.q taylorRow1085.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1085 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link114

theorem actual_link115 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 115) 1 f ε s v=source1040 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1040.q taylorRow1040.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1040.q taylorRow1040.source 0 s*
      sampleSum 210 (by decide) taylorRow1040.q taylorRow1040.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1040 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link115

theorem actual_link116 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 116) 1 f ε s v=source1261 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1261 f ha hu hv s v).symm
#print axioms actual_link116

theorem actual_link117 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 117) 1 f ε s v=source1279 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1279 f ha hu hv s v).symm
#print axioms actual_link117

theorem actual_link118 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 118) 1 f ε s v=source1038 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1038.q taylorRow1038.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1038.q taylorRow1038.source 0 s*
      sampleSum 210 (by decide) taylorRow1038.q taylorRow1038.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1038 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link118

theorem actual_link119 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 119) 1 f ε s v=source1339 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1339 f ha hu hv s v).symm
#print axioms actual_link119

theorem actual_link120 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 120) 1 f ε s v=source1101 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1101.q taylorRow1101.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1101.q taylorRow1101.source 0 s*
      sampleSum 210 (by decide) taylorRow1101.q taylorRow1101.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1101 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link120

theorem actual_link121 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 121) 1 f ε s v=source1124 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1124.q taylorRow1124.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1124.q taylorRow1124.source 0 s*
      sampleSum 210 (by decide) taylorRow1124.q taylorRow1124.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1124 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link121

theorem actual_link122 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 122) 1 f ε s v=source1086 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1086.q taylorRow1086.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1086.q taylorRow1086.source 0 s*
      sampleSum 210 (by decide) taylorRow1086.q taylorRow1086.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1086 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link122

theorem actual_link123 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 123) 1 f ε s v=source1041 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1041.q taylorRow1041.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1041.q taylorRow1041.source 0 s*
      sampleSum 210 (by decide) taylorRow1041.q taylorRow1041.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1041 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link123

theorem actual_link124 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 124) 1 f ε s v=source1277 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1277 f ha hu hv s v).symm
#print axioms actual_link124

theorem actual_link125 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 125) 1 f ε s v=source1039 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1039.q taylorRow1039.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1039.q taylorRow1039.source 0 s*
      sampleSum 210 (by decide) taylorRow1039.q taylorRow1039.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1039 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link125

theorem actual_link126 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 126) 1 f ε s v=source1297 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1297 f ha hu hv s v).symm
#print axioms actual_link126

theorem actual_link127 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 127) 1 f ε s v=source1330 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1330 f ha hu hv s v).symm
#print axioms actual_link127

theorem actual_link128 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 128) 1 f ε s v=source1079 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1079.q taylorRow1079.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1079.q taylorRow1079.source 0 s*
      sampleSum 210 (by decide) taylorRow1079.q taylorRow1079.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1079 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link128

theorem actual_link129 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 129) 1 f ε s v=source1080 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1080.q taylorRow1080.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1080.q taylorRow1080.source 0 s*
      sampleSum 210 (by decide) taylorRow1080.q taylorRow1080.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1080 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link129

theorem actual_link130 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 130) 1 f ε s v=source1083 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1083.q taylorRow1083.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1083.q taylorRow1083.source 0 s*
      sampleSum 210 (by decide) taylorRow1083.q taylorRow1083.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1083 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link130

theorem actual_link131 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 131) 1 f ε s v=source1084 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1084.q taylorRow1084.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1084.q taylorRow1084.source 0 s*
      sampleSum 210 (by decide) taylorRow1084.q taylorRow1084.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1084 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link131

theorem actual_link132 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 132) 1 f ε s v=source1127 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1127.q taylorRow1127.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1127.q taylorRow1127.source 0 s*
      sampleSum 210 (by decide) taylorRow1127.q taylorRow1127.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1127 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link132

theorem actual_link133 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 133) 1 f ε s v=source1150 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1150.q taylorRow1150.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1150.q taylorRow1150.source 0 s*
      sampleSum 210 (by decide) taylorRow1150.q taylorRow1150.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1150 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link133

theorem actual_link134 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 134) 1 f ε s v=source1151 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1151.q taylorRow1151.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1151.q taylorRow1151.source 0 s*
      sampleSum 210 (by decide) taylorRow1151.q taylorRow1151.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1151 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link134

theorem actual_link135 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 135) 1 f ε s v=source1174 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1174.q taylorRow1174.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1174.q taylorRow1174.source 0 s*
      sampleSum 210 (by decide) taylorRow1174.q taylorRow1174.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1174 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link135

theorem actual_link136 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 136) 1 f ε s v=source1175 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1175.q taylorRow1175.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1175.q taylorRow1175.source 0 s*
      sampleSum 210 (by decide) taylorRow1175.q taylorRow1175.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1175 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link136

theorem actual_link137 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 137) 1 f ε s v=source1204 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1204.q taylorRow1204.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1204.q taylorRow1204.source 0 s*
      sampleSum 210 (by decide) taylorRow1204.q taylorRow1204.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1204 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link137

theorem actual_link138 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 138) 1 f ε s v=source1205 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1205.q taylorRow1205.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1205.q taylorRow1205.source 0 s*
      sampleSum 210 (by decide) taylorRow1205.q taylorRow1205.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1205 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link138

theorem actual_link139 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 139) 1 f ε s v=source1251 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1251 f ha hu hv s v).symm
#print axioms actual_link139

theorem actual_link140 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 140) 1 f ε s v=source1254 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1254 f ha hu hv s v).symm
#print axioms actual_link140

theorem actual_link141 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 141) 1 f ε s v=source1255 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1255 f ha hu hv s v).symm
#print axioms actual_link141

theorem actual_link142 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 142) 1 f ε s v=source1260 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1260 f ha hu hv s v).symm
#print axioms actual_link142

theorem actual_link143 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 143) 1 f ε s v=source1267 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1267 f ha hu hv s v).symm
#print axioms actual_link143

theorem actual_link144 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 144) 1 f ε s v=source1270 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1270 f ha hu hv s v).symm
#print axioms actual_link144

theorem actual_link145 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 145) 1 f ε s v=source1276 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1276 f ha hu hv s v).symm
#print axioms actual_link145

theorem actual_link146 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 146) 1 f ε s v=source1280 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1280 f ha hu hv s v).symm
#print axioms actual_link146

theorem actual_link147 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 147) 1 f ε s v=source1282 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1282 f ha hu hv s v).symm
#print axioms actual_link147

theorem actual_link148 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 148) 1 f ε s v=source1185 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1185.q taylorRow1185.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1185.q taylorRow1185.source 0 s*
      sampleSum 210 (by decide) taylorRow1185.q taylorRow1185.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1185 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link148

theorem actual_link149 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 149) 1 f ε s v=source1186 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1186.q taylorRow1186.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1186.q taylorRow1186.source 0 s*
      sampleSum 210 (by decide) taylorRow1186.q taylorRow1186.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1186 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link149

theorem actual_link150 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 150) 1 f ε s v=source1291 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1291 f ha hu hv s v).symm
#print axioms actual_link150

theorem actual_link151 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 151) 1 f ε s v=source1295 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1295 f ha hu hv s v).symm
#print axioms actual_link151

theorem actual_link152 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 152) 1 f ε s v=source1296 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1296 f ha hu hv s v).symm
#print axioms actual_link152

theorem actual_link153 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 153) 1 f ε s v=source1300 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1300 f ha hu hv s v).symm
#print axioms actual_link153

theorem actual_link154 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 154) 1 f ε s v=source1118 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1118.q taylorRow1118.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1118.q taylorRow1118.source 0 s*
      sampleSum 210 (by decide) taylorRow1118.q taylorRow1118.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1118 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link154

theorem actual_link155 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 155) 1 f ε s v=source1311 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1311 f ha hu hv s v).symm
#print axioms actual_link155

theorem actual_link156 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 156) 1 f ε s v=source1321 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1321 f ha hu hv s v).symm
#print axioms actual_link156

theorem actual_link157 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 157) 1 f ε s v=source1117 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1117.q taylorRow1117.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1117.q taylorRow1117.source 0 s*
      sampleSum 210 (by decide) taylorRow1117.q taylorRow1117.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1117 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link157

theorem actual_link158 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 158) 1 f ε s v=source1331 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1331 f ha hu hv s v).symm
#print axioms actual_link158

theorem actual_link159 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 159) 1 f ε s v=source1337 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1337 f ha hu hv s v).symm
#print axioms actual_link159

theorem actual_link160 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 160) 1 f ε s v=source1340 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1340 f ha hu hv s v).symm
#print axioms actual_link160

theorem actual_link161 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 161) 1 f ε s v=source1351 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1351 f ha hu hv s v).symm
#print axioms actual_link161

theorem actual_link162 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 162) 1 f ε s v=source1354 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1354 f ha hu hv s v).symm
#print axioms actual_link162

theorem actual_link163 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 163) 1 f ε s v=source1356 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1356 f ha hu hv s v).symm
#print axioms actual_link163

theorem actual_link164 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 164) 1 f ε s v=source1359 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1359 f ha hu hv s v).symm
#print axioms actual_link164

theorem actual_link165 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 165) 1 f ε s v=source1360 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1360 f ha hu hv s v).symm
#print axioms actual_link165

theorem actual_link166 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 166) 1 f ε s v=source1364 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1364 f ha hu hv s v).symm
#print axioms actual_link166

theorem actual_link167 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 167) 1 f ε s v=source1317 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1317 f ha hu hv s v).symm
#print axioms actual_link167

theorem actual_link168 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 168) 1 f ε s v=source1365 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1365 f ha hu hv s v).symm
#print axioms actual_link168

theorem actual_link169 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 169) 1 f ε s v=source1366 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1366 f ha hu hv s v).symm
#print axioms actual_link169

theorem actual_link170 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 170) 1 f ε s v=source1367 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1367 f ha hu hv s v).symm
#print axioms actual_link170

theorem actual_link171 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 171) 1 f ε s v=source1370 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1370 f ha hu hv s v).symm
#print axioms actual_link171

theorem actual_link172 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 172) 1 f ε s v=source1329 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1329 f ha hu hv s v).symm
#print axioms actual_link172

theorem actual_link173 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 173) 1 f ε s v=source1286 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1286 f ha hu hv s v).symm
#print axioms actual_link173

theorem actual_link174 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 174) 1 f ε s v=source1372 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1372 f ha hu hv s v).symm
#print axioms actual_link174

theorem actual_link175 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 175) 1 f ε s v=source1377 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1377 f ha hu hv s v).symm
#print axioms actual_link175

theorem actual_link176 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 176) 1 f ε s v=source1379 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1379 f ha hu hv s v).symm
#print axioms actual_link176

theorem actual_link177 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 177) 1 f ε s v=source1380 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1380 f ha hu hv s v).symm
#print axioms actual_link177

theorem actual_link178 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 178) 1 f ε s v=source1259 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1259 f ha hu hv s v).symm
#print axioms actual_link178

theorem actual_link179 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 179) 1 f ε s v=source1381 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1381 f ha hu hv s v).symm
#print axioms actual_link179

theorem actual_link180 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 180) 1 f ε s v=source1274 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1274 f ha hu hv s v).symm
#print axioms actual_link180

theorem actual_link181 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 181) 1 f ε s v=source1262 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1262 f ha hu hv s v).symm
#print axioms actual_link181

theorem actual_link182 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 182) 1 f ε s v=source1305 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1305 f ha hu hv s v).symm
#print axioms actual_link182

theorem actual_link183 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 183) 1 f ε s v=source1332 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1332 f ha hu hv s v).symm
#print axioms actual_link183

theorem actual_link184 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 184) 1 f ε s v=source1389 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1389 f ha hu hv s v).symm
#print axioms actual_link184

theorem actual_link185 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 185) 1 f ε s v=source1394 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1394 f ha hu hv s v).symm
#print axioms actual_link185

theorem actual_link186 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 186) 1 f ε s v=source1406 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1406 f ha hu hv s v).symm
#print axioms actual_link186

theorem actual_link187 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 187) 1 f ε s v=source1407 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1407 f ha hu hv s v).symm
#print axioms actual_link187

theorem actual_link188 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 188) 1 f ε s v=source1415 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1415 f ha hu hv s v).symm
#print axioms actual_link188

theorem actual_link189 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 189) 1 f ε s v=source1509 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1509 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v).symm
#print axioms actual_link189

theorem actual_link190 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 190) 1 f ε s v=source1513 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1513 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v).symm
#print axioms actual_link190

theorem actual_link191 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 191) 1 f ε s v=source1075 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1075.q taylorRow1075.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1075.q taylorRow1075.source 0 s*
      sampleSum 210 (by decide) taylorRow1075.q taylorRow1075.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1075 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link191

theorem actual_link192 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 192) 1 f ε s v=source1076 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1076.q taylorRow1076.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1076.q taylorRow1076.source 0 s*
      sampleSum 210 (by decide) taylorRow1076.q taylorRow1076.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1076 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link192

theorem actual_link193 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 193) 1 f ε s v=source1077 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1077.q taylorRow1077.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1077.q taylorRow1077.source 0 s*
      sampleSum 210 (by decide) taylorRow1077.q taylorRow1077.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1077 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link193

theorem actual_link194 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 194) 1 f ε s v=source1078 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1078.q taylorRow1078.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1078.q taylorRow1078.source 0 s*
      sampleSum 210 (by decide) taylorRow1078.q taylorRow1078.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1078 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link194

theorem actual_link195 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 195) 1 f ε s v=source1081 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1081.q taylorRow1081.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1081.q taylorRow1081.source 0 s*
      sampleSum 210 (by decide) taylorRow1081.q taylorRow1081.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1081 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link195

theorem actual_link196 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 196) 1 f ε s v=source1082 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1082.q taylorRow1082.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1082.q taylorRow1082.source 0 s*
      sampleSum 210 (by decide) taylorRow1082.q taylorRow1082.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1082 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link196

theorem actual_link197 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 197) 1 f ε s v=source1113 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1113.q taylorRow1113.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1113.q taylorRow1113.source 0 s*
      sampleSum 210 (by decide) taylorRow1113.q taylorRow1113.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1113 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link197

theorem actual_link198 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 198) 1 f ε s v=source1114 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1114.q taylorRow1114.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1114.q taylorRow1114.source 0 s*
      sampleSum 210 (by decide) taylorRow1114.q taylorRow1114.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1114 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link198

theorem actual_link199 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 199) 1 f ε s v=source1119 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1119.q taylorRow1119.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1119.q taylorRow1119.source 0 s*
      sampleSum 210 (by decide) taylorRow1119.q taylorRow1119.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1119 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link199

theorem actual_link200 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 200) 1 f ε s v=source1172 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1172.q taylorRow1172.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1172.q taylorRow1172.source 0 s*
      sampleSum 210 (by decide) taylorRow1172.q taylorRow1172.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1172 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link200

theorem actual_link201 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 201) 1 f ε s v=source1173 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1173.q taylorRow1173.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1173.q taylorRow1173.source 0 s*
      sampleSum 210 (by decide) taylorRow1173.q taylorRow1173.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1173 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link201

theorem actual_link202 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 202) 1 f ε s v=source1256 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1256 f ha hu hv s v).symm
#print axioms actual_link202

theorem actual_link203 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 203) 1 f ε s v=source1265 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1265 f ha hu hv s v).symm
#print axioms actual_link203

theorem actual_link204 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 204) 1 f ε s v=source1275 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1275 f ha hu hv s v).symm
#print axioms actual_link204

theorem actual_link205 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 205) 1 f ε s v=source1281 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  exact (other_link1281 f ha hu hv s v).symm
#print axioms actual_link205

theorem actual_link206 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 206) 1 f ε s v=source1209 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1209.q taylorRow1209.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1209.q taylorRow1209.source 0 s*
      sampleSum 210 (by decide) taylorRow1209.q taylorRow1209.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1209 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link206

theorem actual_link207 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 207) 1 f ε s v=source1210 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1210.q taylorRow1210.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1210.q taylorRow1210.source 0 s*
      sampleSum 210 (by decide) taylorRow1210.q taylorRow1210.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1210 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link207

theorem actual_link208 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 208) 1 f ε s v=source1116 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1116.q taylorRow1116.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1116.q taylorRow1116.source 0 s*
      sampleSum 210 (by decide) taylorRow1116.q taylorRow1116.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1116 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link208

theorem actual_link209 (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    leading (selectedData 209) 1 f ε s v=source1115 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  change sampleSum 210 (by decide) taylorRow1115.q taylorRow1115.source v-
    taylorCoefficient 210 (2*1) f ε taylorRow1115.q taylorRow1115.source 0 s*
      sampleSum 210 (by decide) taylorRow1115.q taylorRow1115.target v=_
  rw [taylor_certificate_leading,hE,hu,hv]
  exact (taylor_link1115 (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s)
    (hp 2 (by decide)) (hp 3 (by decide)) (hp 7 (by decide)) (hp 5 (by decide)) v).symm
#print axioms actual_link209

end SmallLevelTwentyOneLargeGridLinks
end
end

/-! ## SmallLevelTwentyOneLargeGridLinksTheoryV4 -/
section
/-! Consolidated chapter: SmallLevelTwentyOneLargeGridLinks. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyOneLargeGridActualMatrixV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneLargeGridLinks
open Complex SmallLevelTwentyOneLargeGridAlgebra SmallLevelTwentyOneLargeGridModel
open SmallLevelTwentyOneKnownWords

theorem actual_selected_rows (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) (v : Fin 210 → ℂ) :
    (fun i => leading (selectedData i) 1 f ε s v)=selectedRow (primeParameter 2 1 s) (primeParameter 3 1 s) (primeParameter 7 1 s) (primeParameter 5 1 s) v := by
  funext i
  fin_cases i
  · exact actual_link000 f ε hE hu hv ha s v
  · exact actual_link001 f ε hE hu hv ha s v
  · exact actual_link002 f ε hE hu hv ha s v
  · exact actual_link003 f ε hE hu hv ha s v
  · exact actual_link004 f ε hE hu hv ha s v
  · exact actual_link005 f ε hE hu hv ha s v
  · exact actual_link006 f ε hE hu hv ha s v
  · exact actual_link007 f ε hE hu hv ha s v
  · exact actual_link008 f ε hE hu hv ha s v
  · exact actual_link009 f ε hE hu hv ha s v
  · exact actual_link010 f ε hE hu hv ha s v
  · exact actual_link011 f ε hE hu hv ha s v
  · exact actual_link012 f ε hE hu hv ha s v
  · exact actual_link013 f ε hE hu hv ha s v
  · exact actual_link014 f ε hE hu hv ha s v
  · exact actual_link015 f ε hE hu hv ha s v
  · exact actual_link016 f ε hE hu hv ha s v
  · exact actual_link017 f ε hE hu hv ha s v
  · exact actual_link018 f ε hE hu hv ha s v
  · exact actual_link019 f ε hE hu hv ha s v
  · exact actual_link020 f ε hE hu hv ha s v
  · exact actual_link021 f ε hE hu hv ha s v
  · exact actual_link022 f ε hE hu hv ha s v
  · exact actual_link023 f ε hE hu hv ha s v
  · exact actual_link024 f ε hE hu hv ha s v
  · exact actual_link025 f ε hE hu hv ha s v
  · exact actual_link026 f ε hE hu hv ha s v
  · exact actual_link027 f ε hE hu hv ha s v
  · exact actual_link028 f ε hE hu hv ha s v
  · exact actual_link029 f ε hE hu hv ha s v
  · exact actual_link030 f ε hE hu hv ha s v
  · exact actual_link031 f ε hE hu hv ha s v
  · exact actual_link032 f ε hE hu hv ha s v
  · exact actual_link033 f ε hE hu hv ha s v
  · exact actual_link034 f ε hE hu hv ha s v
  · exact actual_link035 f ε hE hu hv ha s v
  · exact actual_link036 f ε hE hu hv ha s v
  · exact actual_link037 f ε hE hu hv ha s v
  · exact actual_link038 f ε hE hu hv ha s v
  · exact actual_link039 f ε hE hu hv ha s v
  · exact actual_link040 f ε hE hu hv ha s v
  · exact actual_link041 f ε hE hu hv ha s v
  · exact actual_link042 f ε hE hu hv ha s v
  · exact actual_link043 f ε hE hu hv ha s v
  · exact actual_link044 f ε hE hu hv ha s v
  · exact actual_link045 f ε hE hu hv ha s v
  · exact actual_link046 f ε hE hu hv ha s v
  · exact actual_link047 f ε hE hu hv ha s v
  · exact actual_link048 f ε hE hu hv ha s v
  · exact actual_link049 f ε hE hu hv ha s v
  · exact actual_link050 f ε hE hu hv ha s v
  · exact actual_link051 f ε hE hu hv ha s v
  · exact actual_link052 f ε hE hu hv ha s v
  · exact actual_link053 f ε hE hu hv ha s v
  · exact actual_link054 f ε hE hu hv ha s v
  · exact actual_link055 f ε hE hu hv ha s v
  · exact actual_link056 f ε hE hu hv ha s v
  · exact actual_link057 f ε hE hu hv ha s v
  · exact actual_link058 f ε hE hu hv ha s v
  · exact actual_link059 f ε hE hu hv ha s v
  · exact actual_link060 f ε hE hu hv ha s v
  · exact actual_link061 f ε hE hu hv ha s v
  · exact actual_link062 f ε hE hu hv ha s v
  · exact actual_link063 f ε hE hu hv ha s v
  · exact actual_link064 f ε hE hu hv ha s v
  · exact actual_link065 f ε hE hu hv ha s v
  · exact actual_link066 f ε hE hu hv ha s v
  · exact actual_link067 f ε hE hu hv ha s v
  · exact actual_link068 f ε hE hu hv ha s v
  · exact actual_link069 f ε hE hu hv ha s v
  · exact actual_link070 f ε hE hu hv ha s v
  · exact actual_link071 f ε hE hu hv ha s v
  · exact actual_link072 f ε hE hu hv ha s v
  · exact actual_link073 f ε hE hu hv ha s v
  · exact actual_link074 f ε hE hu hv ha s v
  · exact actual_link075 f ε hE hu hv ha s v
  · exact actual_link076 f ε hE hu hv ha s v
  · exact actual_link077 f ε hE hu hv ha s v
  · exact actual_link078 f ε hE hu hv ha s v
  · exact actual_link079 f ε hE hu hv ha s v
  · exact actual_link080 f ε hE hu hv ha s v
  · exact actual_link081 f ε hE hu hv ha s v
  · exact actual_link082 f ε hE hu hv ha s v
  · exact actual_link083 f ε hE hu hv ha s v
  · exact actual_link084 f ε hE hu hv ha s v
  · exact actual_link085 f ε hE hu hv ha s v
  · exact actual_link086 f ε hE hu hv ha s v
  · exact actual_link087 f ε hE hu hv ha s v
  · exact actual_link088 f ε hE hu hv ha s v
  · exact actual_link089 f ε hE hu hv ha s v
  · exact actual_link090 f ε hE hu hv ha s v
  · exact actual_link091 f ε hE hu hv ha s v
  · exact actual_link092 f ε hE hu hv ha s v
  · exact actual_link093 f ε hE hu hv ha s v
  · exact actual_link094 f ε hE hu hv ha s v
  · exact actual_link095 f ε hE hu hv ha s v
  · exact actual_link096 f ε hE hu hv ha s v
  · exact actual_link097 f ε hE hu hv ha s v
  · exact actual_link098 f ε hE hu hv ha s v
  · exact actual_link099 f ε hE hu hv ha s v
  · exact actual_link100 f ε hE hu hv ha s v
  · exact actual_link101 f ε hE hu hv ha s v
  · exact actual_link102 f ε hE hu hv ha s v
  · exact actual_link103 f ε hE hu hv ha s v
  · exact actual_link104 f ε hE hu hv ha s v
  · exact actual_link105 f ε hE hu hv ha s v
  · exact actual_link106 f ε hE hu hv ha s v
  · exact actual_link107 f ε hE hu hv ha s v
  · exact actual_link108 f ε hE hu hv ha s v
  · exact actual_link109 f ε hE hu hv ha s v
  · exact actual_link110 f ε hE hu hv ha s v
  · exact actual_link111 f ε hE hu hv ha s v
  · exact actual_link112 f ε hE hu hv ha s v
  · exact actual_link113 f ε hE hu hv ha s v
  · exact actual_link114 f ε hE hu hv ha s v
  · exact actual_link115 f ε hE hu hv ha s v
  · exact actual_link116 f ε hE hu hv ha s v
  · exact actual_link117 f ε hE hu hv ha s v
  · exact actual_link118 f ε hE hu hv ha s v
  · exact actual_link119 f ε hE hu hv ha s v
  · exact actual_link120 f ε hE hu hv ha s v
  · exact actual_link121 f ε hE hu hv ha s v
  · exact actual_link122 f ε hE hu hv ha s v
  · exact actual_link123 f ε hE hu hv ha s v
  · exact actual_link124 f ε hE hu hv ha s v
  · exact actual_link125 f ε hE hu hv ha s v
  · exact actual_link126 f ε hE hu hv ha s v
  · exact actual_link127 f ε hE hu hv ha s v
  · exact actual_link128 f ε hE hu hv ha s v
  · exact actual_link129 f ε hE hu hv ha s v
  · exact actual_link130 f ε hE hu hv ha s v
  · exact actual_link131 f ε hE hu hv ha s v
  · exact actual_link132 f ε hE hu hv ha s v
  · exact actual_link133 f ε hE hu hv ha s v
  · exact actual_link134 f ε hE hu hv ha s v
  · exact actual_link135 f ε hE hu hv ha s v
  · exact actual_link136 f ε hE hu hv ha s v
  · exact actual_link137 f ε hE hu hv ha s v
  · exact actual_link138 f ε hE hu hv ha s v
  · exact actual_link139 f ε hE hu hv ha s v
  · exact actual_link140 f ε hE hu hv ha s v
  · exact actual_link141 f ε hE hu hv ha s v
  · exact actual_link142 f ε hE hu hv ha s v
  · exact actual_link143 f ε hE hu hv ha s v
  · exact actual_link144 f ε hE hu hv ha s v
  · exact actual_link145 f ε hE hu hv ha s v
  · exact actual_link146 f ε hE hu hv ha s v
  · exact actual_link147 f ε hE hu hv ha s v
  · exact actual_link148 f ε hE hu hv ha s v
  · exact actual_link149 f ε hE hu hv ha s v
  · exact actual_link150 f ε hE hu hv ha s v
  · exact actual_link151 f ε hE hu hv ha s v
  · exact actual_link152 f ε hE hu hv ha s v
  · exact actual_link153 f ε hE hu hv ha s v
  · exact actual_link154 f ε hE hu hv ha s v
  · exact actual_link155 f ε hE hu hv ha s v
  · exact actual_link156 f ε hE hu hv ha s v
  · exact actual_link157 f ε hE hu hv ha s v
  · exact actual_link158 f ε hE hu hv ha s v
  · exact actual_link159 f ε hE hu hv ha s v
  · exact actual_link160 f ε hE hu hv ha s v
  · exact actual_link161 f ε hE hu hv ha s v
  · exact actual_link162 f ε hE hu hv ha s v
  · exact actual_link163 f ε hE hu hv ha s v
  · exact actual_link164 f ε hE hu hv ha s v
  · exact actual_link165 f ε hE hu hv ha s v
  · exact actual_link166 f ε hE hu hv ha s v
  · exact actual_link167 f ε hE hu hv ha s v
  · exact actual_link168 f ε hE hu hv ha s v
  · exact actual_link169 f ε hE hu hv ha s v
  · exact actual_link170 f ε hE hu hv ha s v
  · exact actual_link171 f ε hE hu hv ha s v
  · exact actual_link172 f ε hE hu hv ha s v
  · exact actual_link173 f ε hE hu hv ha s v
  · exact actual_link174 f ε hE hu hv ha s v
  · exact actual_link175 f ε hE hu hv ha s v
  · exact actual_link176 f ε hE hu hv ha s v
  · exact actual_link177 f ε hE hu hv ha s v
  · exact actual_link178 f ε hE hu hv ha s v
  · exact actual_link179 f ε hE hu hv ha s v
  · exact actual_link180 f ε hE hu hv ha s v
  · exact actual_link181 f ε hE hu hv ha s v
  · exact actual_link182 f ε hE hu hv ha s v
  · exact actual_link183 f ε hE hu hv ha s v
  · exact actual_link184 f ε hE hu hv ha s v
  · exact actual_link185 f ε hE hu hv ha s v
  · exact actual_link186 f ε hE hu hv ha s v
  · exact actual_link187 f ε hE hu hv ha s v
  · exact actual_link188 f ε hE hu hv ha s v
  · exact actual_link189 f ε hE hu hv ha s v
  · exact actual_link190 f ε hE hu hv ha s v
  · exact actual_link191 f ε hE hu hv ha s v
  · exact actual_link192 f ε hE hu hv ha s v
  · exact actual_link193 f ε hE hu hv ha s v
  · exact actual_link194 f ε hE hu hv ha s v
  · exact actual_link195 f ε hE hu hv ha s v
  · exact actual_link196 f ε hE hu hv ha s v
  · exact actual_link197 f ε hE hu hv ha s v
  · exact actual_link198 f ε hE hu hv ha s v
  · exact actual_link199 f ε hE hu hv ha s v
  · exact actual_link200 f ε hE hu hv ha s v
  · exact actual_link201 f ε hE hu hv ha s v
  · exact actual_link202 f ε hE hu hv ha s v
  · exact actual_link203 f ε hE hu hv ha s v
  · exact actual_link204 f ε hE hu hv ha s v
  · exact actual_link205 f ε hE hu hv ha s v
  · exact actual_link206 f ε hE hu hv ha s v
  · exact actual_link207 f ε hE hu hv ha s v
  · exact actual_link208 f ε hE hu hv ha s v
  · exact actual_link209 f ε hE hu hv ha s v

#print axioms actual_selected_rows
end SmallLevelTwentyOneLargeGridLinks
end
end

/-! ## SmallLevelTwentyOneLargeGridPhysicalRankV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneLargeGridLinks
open Complex Matrix SmallLevelTwentyOneKnownWords SmallLevelTwentyOneLargeGridModel
open SmallLevelTwentyOneLargeGridAlgebra

/-- The actual analytic leading matrix is nonsingular whenever its explicit
physical two-coordinate obstruction is nonzero. -/
theorem actual_leading_det_ne_zero (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ)
    (hx2 : (primeParameter 2 1 s)^2-1≠0)
    (hP : SmallLevelTwentyOneChiFiveObstruction.residual (primeParameter 2 1 s) (primeParameter 3 1 s)≠0) :
    (leadingMatrix selectedData 1 f ε s).det≠0 := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p 1 s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w h
  have hn : leadingMatrix selectedData 1 f ε s *ᵥ (v-w)=0 := by
    rw [Matrix.mulVec_sub,h,sub_self]
  rw [leadingMatrix_mulVec,actual_selected_rows f ε hE hu hv ha] at hn
  exact sub_eq_zero.mp (kernel_zero _ _ _ _ (hp 2 (by decide)) (hp 3 (by decide))
    (hp 7 (by decide)) (hp 5 (by decide)) hx2 hP (v-w) (congrFun hn))

theorem actual_leading_exists_nonsingular (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) :
    ∃ s, (leadingMatrix selectedData 1 f ε s).det≠0 := by
  refine ⟨3,actual_leading_det_ne_zero f ε hE hu hv ha 3 ?_ ?_⟩
  all_goals norm_num [primeParameter,SmallLevelTwentyOneChiFiveObstruction.residual,
    SmallLevelTwentyOneChiFiveObstruction.coefficientA,SmallLevelTwentyOneChiFiveObstruction.coefficientB]

theorem actual_leading_shift_nonsingular (f : ℕ → ℂ) (ε : ℂ)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) {s : ℂ}
    (hs : SmallLevelTwentyOneChiFive.denominator 2 f s=0) (n : ℕ) :
    (leadingMatrix selectedData 1 f ε (s+n)).det≠0 := by
  obtain ⟨hx,hP⟩ := SmallLevelTwentyOneChiFive.shifted_obstruction_nonzero ha hs n
  apply actual_leading_det_ne_zero f ε hE hu hv ha (s+n)
  · simpa only [primeParameter,Nat.cast_one,Nat.cast_ofNat] using hx
  · simpa only [primeParameter,Nat.cast_one,Nat.cast_ofNat] using hP

#print axioms actual_leading_exists_nonsingular
#print axioms actual_leading_shift_nonsingular
end SmallLevelTwentyOneLargeGridLinks
end
end
end
