module
public import QuantitativeArithmeticSmallLevelThirtyThreeKnownWordsTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftRationalTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftLinks
open QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftRational QuantitativeArithmeticSmallLevelThirtyThreeKnownWords QuantitativeArithmeticSmallLevelThirtyThreeLaurent
open SmallLevelFiniteShift QuantitativeArithmeticSevenLaurentRows

theorem row001_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 1) w=row001 w := by
  have hd : rowDerivative (sourceIndex 1)=(33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 1)=v 0 := rfl
  have hs : sourceRows 1=[((1/1:ℚ),0,(0,0,0,0,0,0,0)),((-1/1:ℚ),64,(0,1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 1=sourceKind 1 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (1 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row001] <;> ring

theorem row002_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 2) w=row002 w := by
  have hd : rowDerivative (sourceIndex 2)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 2)=0 := rfl
  have hs : sourceRows 2=[((1/1:ℚ),0,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 2=sourceKind 2 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (2 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row002] <;> ring

theorem row003_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 3) w=row003 w := by
  have hd : rowDerivative (sourceIndex 3)=(1/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 3)=v 1 := rfl
  have hs : sourceRows 3=[((-1/1:ℚ),0,(-2,-1,-1,1,0,0,0)),((1/1:ℚ),1,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 3=sourceKind 3 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (3 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row003] <;> ring

theorem row004_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 4) w=row004 w := by
  have hd : rowDerivative (sourceIndex 4)=(1/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 4)=v 2 := rfl
  have hs : sourceRows 4=[((-1/1:ℚ),0,(0,-1,-1,1,0,0,0)),((1/1:ℚ),2,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 4=sourceKind 4 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (4 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row004] <;> ring

theorem row005_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 5) w=row005 w := by
  have hd : rowDerivative (sourceIndex 5)=(3/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 5)=v 3 := rfl
  have hs : sourceRows 5=[((1/1:ℚ),3,(0,0,0,0,0,0,0)),((-1/1:ℚ),22,(-2,1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 5=sourceKind 5 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (5 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row005] <;> ring

theorem row006_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 6) w=row006 w := by
  have hd : rowDerivative (sourceIndex 6)=(2/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 6)=v 4 := rfl
  have hs : sourceRows 6=[((1/1:ℚ),4,(0,0,0,0,0,0,0)),((-1/1:ℚ),33,(2,-1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 6=sourceKind 6 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (6 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row006] <;> ring

theorem row007_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 7) w=row007 w := by
  have hd : rowDerivative (sourceIndex 7)=(3/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 7)=v 6 := rfl
  have hs : sourceRows 7=[((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),44,(0,1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 7=sourceKind 7 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (7 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row007] <;> ring

theorem row008_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 8) w=row008 w := by
  have hd : rowDerivative (sourceIndex 8)=(11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 8)=v 11 := rfl
  have hs : sourceRows 8=[((1/1:ℚ),11,(0,0,0,0,0,0,0)),((-1/1:ℚ),54,(-2,-1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 8=sourceKind 8 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (8 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row008] <;> ring

theorem row009_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 9) w=row009 w := by
  have hd : rowDerivative (sourceIndex 9)=(6/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 9)=v 12 := rfl
  have hs : sourceRows 9=[((1/1:ℚ),12,(0,0,0,0,0,0,0)),((-1/1:ℚ),55,(2,1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 9=sourceKind 9 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (9 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row009] <;> ring

theorem row010_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 10) w=row010 w := by
  have hd : rowDerivative (sourceIndex 10)=(11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 10)=v 22 := rfl
  have hs : sourceRows 10=[((1/1:ℚ),22,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(0,-1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 10=sourceKind 10 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (10 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row010] <;> ring

theorem row011_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 11) w=row011 w := by
  have hd : rowDerivative (sourceIndex 11)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 11)=v 33 := rfl
  have hs : sourceRows 11=[((1/1:ℚ),33,(0,0,0,0,0,0,0)),((-1/1:ℚ),62,(-2,1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 11=sourceKind 11 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (11 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row011] <;> ring

theorem row012_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 12) w=row012 w := by
  have hd : rowDerivative (sourceIndex 12)=(22/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 12)=v 44 := rfl
  have hs : sourceRows 12=[((1/1:ℚ),44,(0,0,0,0,0,0,0)),((-1/1:ℚ),63,(2,-1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 12=sourceKind 12 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (12 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row012] <;> ring

theorem row013_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 43) w=row013 w := by
  have hd : rowDerivative (sourceIndex 43)=(-165/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 43)=v 33 := rfl
  have hs : sourceRows 43=[((-1/1:ℚ),0,(-2,0,0,0,0,0,0)),((1/1:ℚ),33,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 43=sourceKind 43 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (43 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row013] <;> ring

theorem row014_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 44) w=row014 w := by
  have hd : rowDerivative (sourceIndex 44)=(330/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 44)=v 34 := rfl
  have hs : sourceRows 44=[((1/1:ℚ),34,(0,0,0,0,0,0,0)),((-1/1:ℚ),65,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 44=sourceKind 44 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (44 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row014] <;> ring

theorem row015_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 45) w=row015 w := by
  have hd : rowDerivative (sourceIndex 45)=(-198/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 45)=v 32 := rfl
  have hs : sourceRows 45=[((1/1:ℚ),32,(0,0,0,0,0,0,0)),((-1/1:ℚ),65,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 45=sourceKind 45 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (45 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row015] <;> ring

theorem row016_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 48) w=row016 w := by
  have hd : rowDerivative (sourceIndex 48)=(-66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 48)=v 30 := rfl
  have hs : sourceRows 48=[((1/1:ℚ),30,(0,0,0,0,0,0,0)),((-1/1:ℚ),63,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 48=sourceKind 48 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (48 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row016] <;> ring

theorem row017_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 52) w=row017 w := by
  have hd : rowDerivative (sourceIndex 52)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 52)=v 35 := rfl
  have hs : sourceRows 52=[((1/1:ℚ),35,(0,0,0,0,0,0,0)),((-1/1:ℚ),58,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 52=sourceKind 52 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (52 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row017] <;> ring

theorem row018_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 53) w=row018 w := by
  have hd : rowDerivative (sourceIndex 53)=(33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 53)=v 36 := rfl
  have hs : sourceRows 53=[((1/1:ℚ),36,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 53=sourceKind 53 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (53 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row018] <;> ring

theorem row019_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 54) w=row019 w := by
  have hd : rowDerivative (sourceIndex 54)=(66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 54)=v 38 := rfl
  have hs : sourceRows 54=[((1/1:ℚ),38,(0,0,0,0,0,0,0)),((-1/1:ℚ),61,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 54=sourceKind 54 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (54 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row019] <;> ring

theorem row020_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 55) w=row020 w := by
  have hd : rowDerivative (sourceIndex 55)=(-66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 55)=v 28 := rfl
  have hs : sourceRows 55=[((-1/1:ℚ),5,(2,0,0,0,0,0,0)),((1/1:ℚ),28,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 55=sourceKind 55 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (55 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row020] <;> ring

theorem row021_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 57) w=row021 w := by
  have hd : rowDerivative (sourceIndex 57)=(-33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 57)=v 31 := rfl
  have hs : sourceRows 57=[((-1/1:ℚ),8,(-2,0,0,0,0,0,0)),((1/1:ℚ),31,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 57=sourceKind 57 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (57 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row021] <;> ring

theorem row022_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 65) w=row022 w := by
  have hd : rowDerivative (sourceIndex 65)=(-165/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 65)=v 54 := rfl
  have hs : sourceRows 65=[((1/1:ℚ),54,(0,0,0,0,0,0,0)),((1/1:ℚ),64,(0,1,0,0,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 65=sourceKind 65 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (65 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row022] <;> ring

theorem row023_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 66) w=row023 w := by
  have hd : rowDerivative (sourceIndex 66)=(-55/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 66)=v 55 := rfl
  have hs : sourceRows 66=[((1/1:ℚ),0,(-2,-1,0,0,0,1,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 66=sourceKind 66 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (66 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row023] <;> ring

theorem row024_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 67) w=row024 w := by
  have hd : rowDerivative (sourceIndex 67)=(110/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 67)=v 56 := rfl
  have hs : sourceRows 67=[((1/1:ℚ),56,(0,0,0,0,0,0,0)),((1/1:ℚ),63,(2,-1,0,0,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 67=sourceKind 67 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (67 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row024] <;> ring

theorem row025_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 68) w=row025 w := by
  have hd : rowDerivative (sourceIndex 68)=(-66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 68)=v 42 := rfl
  have hs : sourceRows 68=[((1/1:ℚ),13,(2,1,0,0,0,1,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 68=sourceKind 68 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (68 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row025] <;> ring

theorem row026_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 69) w=row026 w := by
  have hd : rowDerivative (sourceIndex 69)=(-33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 69)=v 48 := rfl
  have hs : sourceRows 69=[((1/1:ℚ),14,(0,1,0,0,0,1,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 69=sourceKind 69 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (69 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row026] <;> ring

theorem row027_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 70) w=row027 w := by
  have hd : rowDerivative (sourceIndex 70)=(-22/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 70)=v 50 := rfl
  have hs : sourceRows 70=[((1/1:ℚ),15,(2,-1,0,0,0,1,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 70=sourceKind 70 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (70 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row027] <;> ring

theorem row028_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 71) w=row028 w := by
  have hd : rowDerivative (sourceIndex 71)=(-33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 71)=v 51 := rfl
  have hs : sourceRows 71=[((1/1:ℚ),16,(-2,1,0,0,0,1,0)),((1/1:ℚ),51,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 71=sourceKind 71 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (71 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row028] <;> ring

theorem row029_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 72) w=row029 w := by
  have hd : rowDerivative (sourceIndex 72)=(-11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 72)=v 52 := rfl
  have hs : sourceRows 72=[((1/1:ℚ),18,(0,-1,0,0,0,1,0)),((1/1:ℚ),52,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 72=sourceKind 72 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (72 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row029] <;> ring

theorem row030_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 73) w=row030 w := by
  have hd : rowDerivative (sourceIndex 73)=(-11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 73)=v 53 := rfl
  have hs : sourceRows 73=[((1/1:ℚ),24,(-2,-1,0,0,0,1,0)),((1/1:ℚ),53,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 73=sourceKind 73 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (73 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row030] <;> ring

theorem row031_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 77) w=row031 w := by
  have hd : rowDerivative (sourceIndex 77)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 77)=v 57 := rfl
  have hs : sourceRows 77=[((1/1:ℚ),8,(-2,1,0,0,0,1,0)),((1/1:ℚ),57,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 77=sourceKind 77 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (77 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row031] <;> ring

theorem row032_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 78) w=row032 w := by
  have hd : rowDerivative (sourceIndex 78)=(22/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 78)=v 58 := rfl
  have hs : sourceRows 78=[((1/1:ℚ),9,(2,-1,0,0,0,1,0)),((1/1:ℚ),58,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 78=sourceKind 78 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (78 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row032] <;> ring

theorem row033_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 79) w=row033 w := by
  have hd : rowDerivative (sourceIndex 79)=(33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 79)=v 60 := rfl
  have hs : sourceRows 79=[((1/1:ℚ),10,(0,1,0,0,0,1,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 79=sourceKind 79 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (79 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row033] <;> ring

theorem row034_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 668) w=row034 w := by
  have hd : rowDerivative (sourceIndex 668)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 668)=0 := rfl
  have hs : sourceRows 668=[((1/1:ℚ),22,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 668=sourceKind 668 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (668 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row034] <;> ring

theorem row035_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 669) w=row035 w := by
  have hd : rowDerivative (sourceIndex 669)=(3/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 669)=gridSample 3 (1) v := rfl
  have hs : sourceRows 669=[((1/1:ℚ),0,(-2,0,-1,1,0,1,0)),((1/1:ℚ),23,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(-2,0,-1,1,0,1,0)),((1/1:ℚ),45,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 669=sourceKind 669 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (669 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row035] <;> ring

theorem row036_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 670) w=row036 w := by
  have hd : rowDerivative (sourceIndex 670)=(-3/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 670)=gridSample 3 (-1) v := rfl
  have hs : sourceRows 670=[((1/1:ℚ),0,(-2,0,-1,1,0,1,0)),((1/1:ℚ),21,(0,0,0,0,0,0,0)),((1/1:ℚ),22,(-2,0,-1,1,0,1,0)),((1/1:ℚ),43,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 670=sourceKind 670 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (670 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row036] <;> ring

theorem row037_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 671) w=row037 w := by
  have hd : rowDerivative (sourceIndex 671)=(3/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 671)=gridSample 3 (2) v := rfl
  have hs : sourceRows 671=[((1/1:ℚ),0,(0,0,-1,1,0,1,0)),((1/1:ℚ),22,(0,0,-1,1,0,1,0)),((1/1:ℚ),24,(0,0,0,0,0,0,0)),((1/1:ℚ),46,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 671=sourceKind 671 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (671 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row037] <;> ring

theorem row038_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 672) w=row038 w := by
  have hd : rowDerivative (sourceIndex 672)=(-3/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 672)=gridSample 3 (-2) v := rfl
  have hs : sourceRows 672=[((1/1:ℚ),0,(0,0,-1,1,0,1,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(0,0,-1,1,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 672=sourceKind 672 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (672 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row038] <;> ring

theorem row039_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 673) w=row039 w := by
  have hd : rowDerivative (sourceIndex 673)=(6/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 673)=gridSample 3 (4) v := rfl
  have hs : sourceRows 673=[((1/1:ℚ),11,(2,0,-1,1,0,1,0)),((1/1:ℚ),26,(0,0,0,0,0,0,0)),((1/1:ℚ),33,(2,0,-1,1,0,1,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 673=sourceKind 673 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (673 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row039] <;> ring

theorem row040_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 674) w=row040 w := by
  have hd : rowDerivative (sourceIndex 674)=(-6/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 674)=gridSample 3 (-4) v := rfl
  have hs : sourceRows 674=[((1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),33,(2,0,-1,1,0,1,0)),((1/1:ℚ),40,(0,0,0,0,0,0,0)),((1/1:ℚ),55,(2,0,-1,1,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 674=sourceKind 674 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (674 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row040] <;> ring

theorem row041_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 686) w=row041 w := by
  have hd : rowDerivative (sourceIndex 686)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 686)=0 := rfl
  have hs : sourceRows 686=[((1/1:ℚ),6,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 686=sourceKind 686 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (686 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row041] <;> ring

theorem row042_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 687) w=row042 w := by
  have hd : rowDerivative (sourceIndex 687)=(11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 687)=gridSample 11 (1) v := rfl
  have hs : sourceRows 687=[((1/1:ℚ),0,(-2,-1,0,1,0,0,1)),((1/1:ℚ),6,(-2,-1,0,1,0,0,1)),((1/1:ℚ),7,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(-2,-1,0,1,0,0,1)),((1/1:ℚ),13,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(-2,-1,0,1,0,0,1)),((1/1:ℚ),19,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(-2,-1,0,1,0,0,1)),((1/1:ℚ),25,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(-2,-1,0,1,0,0,1)),((1/1:ℚ),31,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(-2,-1,0,1,0,0,1)),((1/1:ℚ),37,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,-1,0,1,0,0,1)),((1/1:ℚ),43,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(-2,-1,0,1,0,0,1)),((1/1:ℚ),49,(0,0,0,0,0,0,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(-2,-1,0,1,0,0,1)),((1/1:ℚ),61,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 687=sourceKind 687 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (687 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row042] <;> ring

theorem row043_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 688) w=row043 w := by
  have hd : rowDerivative (sourceIndex 688)=(-11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 688)=gridSample 11 (-1) v := rfl
  have hs : sourceRows 688=[((1/1:ℚ),0,(-2,-1,0,1,0,0,1)),((1/1:ℚ),5,(0,0,0,0,0,0,0)),((1/1:ℚ),6,(-2,-1,0,1,0,0,1)),((1/1:ℚ),11,(0,0,0,0,0,0,0)),((1/1:ℚ),17,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(-2,-1,0,1,0,0,1)),((1/1:ℚ),23,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(-2,-1,0,1,0,0,1)),((1/1:ℚ),29,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(-2,-1,0,1,0,0,1)),((1/1:ℚ),35,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(-2,-1,0,1,0,0,1)),((1/1:ℚ),41,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,-1,0,1,0,0,1)),((1/1:ℚ),47,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(-2,-1,0,1,0,0,1)),((1/1:ℚ),53,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(-2,-1,0,1,0,0,1)),((1/1:ℚ),59,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(-2,-1,0,1,0,0,1))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 688=sourceKind 688 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (688 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row043] <;> ring

theorem row044_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 689) w=row044 w := by
  have hd : rowDerivative (sourceIndex 689)=(11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 689)=gridSample 11 (2) v := rfl
  have hs : sourceRows 689=[((1/1:ℚ),0,(0,-1,0,1,0,0,1)),((1/1:ℚ),6,(0,-1,0,1,0,0,1)),((1/1:ℚ),8,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(0,-1,0,1,0,0,1)),((1/1:ℚ),14,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,-1,0,1,0,0,1)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,-1,0,1,0,0,1)),((1/1:ℚ),26,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(0,-1,0,1,0,0,1)),((1/1:ℚ),32,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(0,-1,0,1,0,0,1)),((1/1:ℚ),38,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,-1,0,1,0,0,1)),((1/1:ℚ),44,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(0,-1,0,1,0,0,1)),((1/1:ℚ),50,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(0,-1,0,1,0,0,1)),((1/1:ℚ),56,(0,0,0,0,0,0,0)),((1/1:ℚ),62,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 689=sourceKind 689 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (689 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row044] <;> ring

theorem row045_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 690) w=row045 w := by
  have hd : rowDerivative (sourceIndex 690)=(-11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 690)=gridSample 11 (-2) v := rfl
  have hs : sourceRows 690=[((1/1:ℚ),0,(0,-1,0,1,0,0,1)),((1/1:ℚ),4,(0,0,0,0,0,0,0)),((1/1:ℚ),10,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(0,-1,0,1,0,0,1)),((1/1:ℚ),16,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,-1,0,1,0,0,1)),((1/1:ℚ),22,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,-1,0,1,0,0,1)),((1/1:ℚ),28,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(0,-1,0,1,0,0,1)),((1/1:ℚ),34,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(0,-1,0,1,0,0,1)),((1/1:ℚ),40,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,-1,0,1,0,0,1)),((1/1:ℚ),46,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(0,-1,0,1,0,0,1)),((1/1:ℚ),52,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(0,-1,0,1,0,0,1)),((1/1:ℚ),58,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(0,-1,0,1,0,0,1))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 690=sourceKind 690 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (690 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row045] <;> ring

theorem row046_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 691) w=row046 w := by
  have hd : rowDerivative (sourceIndex 691)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 691)=gridSample 11 (3) v := rfl
  have hs : sourceRows 691=[((1/1:ℚ),2,(-2,1,0,1,0,0,1)),((1/1:ℚ),8,(-2,1,0,1,0,0,1)),((1/1:ℚ),9,(0,0,0,0,0,0,0)),((1/1:ℚ),14,(-2,1,0,1,0,0,1)),((1/1:ℚ),15,(0,0,0,0,0,0,0)),((1/1:ℚ),20,(-2,1,0,1,0,0,1)),((1/1:ℚ),21,(0,0,0,0,0,0,0)),((1/1:ℚ),26,(-2,1,0,1,0,0,1)),((1/1:ℚ),27,(0,0,0,0,0,0,0)),((1/1:ℚ),32,(-2,1,0,1,0,0,1)),((1/1:ℚ),33,(0,0,0,0,0,0,0)),((1/1:ℚ),38,(-2,1,0,1,0,0,1)),((1/1:ℚ),39,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(-2,1,0,1,0,0,1)),((1/1:ℚ),45,(0,0,0,0,0,0,0)),((1/1:ℚ),50,(-2,1,0,1,0,0,1)),((1/1:ℚ),51,(0,0,0,0,0,0,0)),((1/1:ℚ),56,(-2,1,0,1,0,0,1)),((1/1:ℚ),57,(0,0,0,0,0,0,0)),((1/1:ℚ),63,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 691=sourceKind 691 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (691 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row046] <;> ring

theorem row047_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 716) w=row047 w := by
  have hd : rowDerivative (sourceIndex 716)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 716)=0 := rfl
  have hs : sourceRows 716=[((1/1:ℚ),2,(0,0,0,0,0,0,0)),((-1/1:ℚ),4,(-1,0,0,0,1,0,0)),((1/1:ℚ),8,(-2,0,0,0,0,0,0)),((1/1:ℚ),35,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 716=sourceKind 716 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (716 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row047] <;> ring

theorem row048_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 718) w=row048 w := by
  have hd : rowDerivative (sourceIndex 718)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 718)=0 := rfl
  have hs : sourceRows 718=[((1/1:ℚ),4,(0,0,0,0,0,0,0)),((-1/1:ℚ),8,(-1,0,0,0,1,0,0)),((1/1:ℚ),16,(-2,0,0,0,0,0,0)),((1/1:ℚ),37,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 718=sourceKind 718 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (718 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row048] <;> ring

theorem row049_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 719) w=row049 w := by
  have hd : rowDerivative (sourceIndex 719)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 719)=0 := rfl
  have hs : sourceRows 719=[((1/1:ℚ),5,(0,0,0,0,0,0,0)),((-1/1:ℚ),10,(-1,0,0,0,1,0,0)),((1/1:ℚ),20,(-2,0,0,0,0,0,0)),((1/1:ℚ),38,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 719=sourceKind 719 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (719 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row049] <;> ring

theorem row050_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 720) w=row050 w := by
  have hd : rowDerivative (sourceIndex 720)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 720)=0 := rfl
  have hs : sourceRows 720=[((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),12,(-1,0,0,0,1,0,0)),((1/1:ℚ),24,(-2,0,0,0,0,0,0)),((1/1:ℚ),39,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 720=sourceKind 720 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (720 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row050] <;> ring

theorem row051_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 721) w=row051 w := by
  have hd : rowDerivative (sourceIndex 721)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 721)=0 := rfl
  have hs : sourceRows 721=[((1/1:ℚ),7,(0,0,0,0,0,0,0)),((-1/1:ℚ),14,(-1,0,0,0,1,0,0)),((1/1:ℚ),28,(-2,0,0,0,0,0,0)),((1/1:ℚ),40,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 721=sourceKind 721 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (721 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row051] <;> ring

theorem row052_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 722) w=row052 w := by
  have hd : rowDerivative (sourceIndex 722)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 722)=0 := rfl
  have hs : sourceRows 722=[((1/1:ℚ),8,(0,0,0,0,0,0,0)),((-1/1:ℚ),16,(-1,0,0,0,1,0,0)),((1/1:ℚ),32,(-2,0,0,0,0,0,0)),((1/1:ℚ),41,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 722=sourceKind 722 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (722 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row052] <;> ring

theorem row053_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 723) w=row053 w := by
  have hd : rowDerivative (sourceIndex 723)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 723)=0 := rfl
  have hs : sourceRows 723=[((1/1:ℚ),9,(0,0,0,0,0,0,0)),((-1/1:ℚ),18,(-1,0,0,0,1,0,0)),((1/1:ℚ),36,(-2,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 723=sourceKind 723 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (723 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row053] <;> ring

theorem row054_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 724) w=row054 w := by
  have hd : rowDerivative (sourceIndex 724)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 724)=0 := rfl
  have hs : sourceRows 724=[((1/1:ℚ),10,(0,0,0,0,0,0,0)),((-1/1:ℚ),20,(-1,0,0,0,1,0,0)),((1/1:ℚ),40,(-2,0,0,0,0,0,0)),((1/1:ℚ),43,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 724=sourceKind 724 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (724 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row054] <;> ring

theorem row055_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 726) w=row055 w := by
  have hd : rowDerivative (sourceIndex 726)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 726)=0 := rfl
  have hs : sourceRows 726=[((1/1:ℚ),12,(0,0,0,0,0,0,0)),((-1/1:ℚ),24,(-1,0,0,0,1,0,0)),((1/1:ℚ),45,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 726=sourceKind 726 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (726 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row055] <;> ring

theorem row056_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 727) w=row056 w := by
  have hd : rowDerivative (sourceIndex 727)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 727)=0 := rfl
  have hs : sourceRows 727=[((1/1:ℚ),13,(0,0,0,0,0,0,0)),((-1/1:ℚ),26,(-1,0,0,0,1,0,0)),((1/1:ℚ),46,(0,0,0,0,0,0,0)),((1/1:ℚ),52,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 727=sourceKind 727 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (727 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row056] <;> ring

theorem row057_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 728) w=row057 w := by
  have hd : rowDerivative (sourceIndex 728)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 728)=0 := rfl
  have hs : sourceRows 728=[((1/1:ℚ),14,(0,0,0,0,0,0,0)),((-1/1:ℚ),28,(-1,0,0,0,1,0,0)),((1/1:ℚ),47,(0,0,0,0,0,0,0)),((1/1:ℚ),56,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 728=sourceKind 728 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (728 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row057] <;> ring

theorem row058_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 729) w=row058 w := by
  have hd : rowDerivative (sourceIndex 729)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 729)=0 := rfl
  have hs : sourceRows 729=[((1/1:ℚ),15,(0,0,0,0,0,0,0)),((-1/1:ℚ),30,(-1,0,0,0,1,0,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 729=sourceKind 729 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (729 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row058] <;> ring

theorem row059_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 730) w=row059 w := by
  have hd : rowDerivative (sourceIndex 730)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 730)=0 := rfl
  have hs : sourceRows 730=[((1/1:ℚ),16,(0,0,0,0,0,0,0)),((-1/1:ℚ),32,(-1,0,0,0,1,0,0)),((1/1:ℚ),49,(0,0,0,0,0,0,0)),((1/1:ℚ),64,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 730=sourceKind 730 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (730 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row059] <;> ring

theorem row060_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 731) w=row060 w := by
  have hd : rowDerivative (sourceIndex 731)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 731)=0 := rfl
  have hs : sourceRows 731=[((1/1:ℚ),2,(-2,0,0,0,0,0,0)),((1/1:ℚ),17,(0,0,0,0,0,0,0)),((-1/1:ℚ),34,(-1,0,0,0,1,0,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 731=sourceKind 731 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (731 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row060] <;> ring

theorem row061_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 732) w=row061 w := by
  have hd : rowDerivative (sourceIndex 732)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 732)=0 := rfl
  have hs : sourceRows 732=[((1/1:ℚ),6,(-2,0,0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,0,0,0)),((-1/1:ℚ),36,(-1,0,0,0,1,0,0)),((1/1:ℚ),51,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 732=sourceKind 732 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (732 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row061] <;> ring

theorem row062_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 733) w=row062 w := by
  have hd : rowDerivative (sourceIndex 733)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 733)=0 := rfl
  have hs : sourceRows 733=[((1/1:ℚ),10,(-2,0,0,0,0,0,0)),((1/1:ℚ),19,(0,0,0,0,0,0,0)),((-1/1:ℚ),38,(-1,0,0,0,1,0,0)),((1/1:ℚ),52,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 733=sourceKind 733 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (733 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row062] <;> ring

theorem row063_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 734) w=row063 w := by
  have hd : rowDerivative (sourceIndex 734)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 734)=0 := rfl
  have hs : sourceRows 734=[((1/1:ℚ),14,(-2,0,0,0,0,0,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((-1/1:ℚ),40,(-1,0,0,0,1,0,0)),((1/1:ℚ),53,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 734=sourceKind 734 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (734 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row063] <;> ring

theorem row064_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 740) w=row064 w := by
  have hd : rowDerivative (sourceIndex 740)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 740)=0 := rfl
  have hs : sourceRows 740=[((1/1:ℚ),26,(0,0,0,0,0,0,0)),((1/1:ℚ),38,(-2,0,0,0,0,0,0)),((-1/1:ℚ),52,(-1,0,0,0,1,0,0)),((1/1:ℚ),59,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 740=sourceKind 740 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (740 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row064] <;> ring

theorem row065_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 0) w=row065 w := by
  have hd : rowDerivative (sourceIndex 0)=(66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 0)=v 0 := rfl
  have hs : sourceRows 0=[((1/1:ℚ),0,(0,0,0,0,0,0,0)),((-1/1:ℚ),65,(2,1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 0=sourceKind 0 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (0 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row065] <;> ring

theorem row066_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 1) w=row066 w := by
  have hd : rowDerivative (sourceIndex 1)=(33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 1)=v 0 := rfl
  have hs : sourceRows 1=[((1/1:ℚ),0,(0,0,0,0,0,0,0)),((-1/1:ℚ),64,(0,1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 1=sourceKind 1 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (1 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row066] <;> ring

theorem row067_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 2) w=row067 w := by
  have hd : rowDerivative (sourceIndex 2)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 2)=0 := rfl
  have hs : sourceRows 2=[((1/1:ℚ),0,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 2=sourceKind 2 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (2 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row067] <;> ring

theorem row068_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 3) w=row068 w := by
  have hd : rowDerivative (sourceIndex 3)=(1/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 3)=v 1 := rfl
  have hs : sourceRows 3=[((-1/1:ℚ),0,(-2,-1,-1,1,0,0,0)),((1/1:ℚ),1,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 3=sourceKind 3 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (3 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row068] <;> ring

theorem row069_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 4) w=row069 w := by
  have hd : rowDerivative (sourceIndex 4)=(1/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 4)=v 2 := rfl
  have hs : sourceRows 4=[((-1/1:ℚ),0,(0,-1,-1,1,0,0,0)),((1/1:ℚ),2,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 4=sourceKind 4 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (4 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row069] <;> ring

theorem row070_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 5) w=row070 w := by
  have hd : rowDerivative (sourceIndex 5)=(3/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 5)=v 3 := rfl
  have hs : sourceRows 5=[((1/1:ℚ),3,(0,0,0,0,0,0,0)),((-1/1:ℚ),22,(-2,1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 5=sourceKind 5 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (5 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row070] <;> ring

theorem row071_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 6) w=row071 w := by
  have hd : rowDerivative (sourceIndex 6)=(2/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 6)=v 4 := rfl
  have hs : sourceRows 6=[((1/1:ℚ),4,(0,0,0,0,0,0,0)),((-1/1:ℚ),33,(2,-1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 6=sourceKind 6 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (6 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row071] <;> ring

theorem row072_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 7) w=row072 w := by
  have hd : rowDerivative (sourceIndex 7)=(3/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 7)=v 6 := rfl
  have hs : sourceRows 7=[((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),44,(0,1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 7=sourceKind 7 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (7 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row072] <;> ring

theorem row073_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 8) w=row073 w := by
  have hd : rowDerivative (sourceIndex 8)=(11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 8)=v 11 := rfl
  have hs : sourceRows 8=[((1/1:ℚ),11,(0,0,0,0,0,0,0)),((-1/1:ℚ),54,(-2,-1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 8=sourceKind 8 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (8 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row073] <;> ring

theorem row074_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 9) w=row074 w := by
  have hd : rowDerivative (sourceIndex 9)=(6/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 9)=v 12 := rfl
  have hs : sourceRows 9=[((1/1:ℚ),12,(0,0,0,0,0,0,0)),((-1/1:ℚ),55,(2,1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 9=sourceKind 9 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (9 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row074] <;> ring

theorem row075_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 10) w=row075 w := by
  have hd : rowDerivative (sourceIndex 10)=(11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 10)=v 22 := rfl
  have hs : sourceRows 10=[((1/1:ℚ),22,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(0,-1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 10=sourceKind 10 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (10 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row075] <;> ring

theorem row076_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 11) w=row076 w := by
  have hd : rowDerivative (sourceIndex 11)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 11)=v 33 := rfl
  have hs : sourceRows 11=[((1/1:ℚ),33,(0,0,0,0,0,0,0)),((-1/1:ℚ),62,(-2,1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 11=sourceKind 11 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (11 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row076] <;> ring

theorem row077_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 12) w=row077 w := by
  have hd : rowDerivative (sourceIndex 12)=(22/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 12)=v 44 := rfl
  have hs : sourceRows 12=[((1/1:ℚ),44,(0,0,0,0,0,0,0)),((-1/1:ℚ),63,(2,-1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 12=sourceKind 12 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (12 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row077] <;> ring

theorem row078_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 43) w=row078 w := by
  have hd : rowDerivative (sourceIndex 43)=(-165/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 43)=v 33 := rfl
  have hs : sourceRows 43=[((-1/1:ℚ),0,(-2,0,0,0,0,0,0)),((1/1:ℚ),33,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 43=sourceKind 43 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (43 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row078] <;> ring

theorem row079_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 44) w=row079 w := by
  have hd : rowDerivative (sourceIndex 44)=(330/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 44)=v 34 := rfl
  have hs : sourceRows 44=[((1/1:ℚ),34,(0,0,0,0,0,0,0)),((-1/1:ℚ),65,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 44=sourceKind 44 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (44 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row079] <;> ring

theorem row080_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 45) w=row080 w := by
  have hd : rowDerivative (sourceIndex 45)=(-198/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 45)=v 32 := rfl
  have hs : sourceRows 45=[((1/1:ℚ),32,(0,0,0,0,0,0,0)),((-1/1:ℚ),65,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 45=sourceKind 45 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (45 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row080] <;> ring

theorem row081_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 48) w=row081 w := by
  have hd : rowDerivative (sourceIndex 48)=(-66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 48)=v 30 := rfl
  have hs : sourceRows 48=[((1/1:ℚ),30,(0,0,0,0,0,0,0)),((-1/1:ℚ),63,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 48=sourceKind 48 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (48 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row081] <;> ring

theorem row082_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 52) w=row082 w := by
  have hd : rowDerivative (sourceIndex 52)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 52)=v 35 := rfl
  have hs : sourceRows 52=[((1/1:ℚ),35,(0,0,0,0,0,0,0)),((-1/1:ℚ),58,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 52=sourceKind 52 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (52 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row082] <;> ring

theorem row083_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 53) w=row083 w := by
  have hd : rowDerivative (sourceIndex 53)=(33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 53)=v 36 := rfl
  have hs : sourceRows 53=[((1/1:ℚ),36,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 53=sourceKind 53 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (53 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row083] <;> ring

theorem row084_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 54) w=row084 w := by
  have hd : rowDerivative (sourceIndex 54)=(66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 54)=v 38 := rfl
  have hs : sourceRows 54=[((1/1:ℚ),38,(0,0,0,0,0,0,0)),((-1/1:ℚ),61,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 54=sourceKind 54 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (54 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row084] <;> ring

theorem row085_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 55) w=row085 w := by
  have hd : rowDerivative (sourceIndex 55)=(-66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 55)=v 28 := rfl
  have hs : sourceRows 55=[((-1/1:ℚ),5,(2,0,0,0,0,0,0)),((1/1:ℚ),28,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 55=sourceKind 55 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (55 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row085] <;> ring

theorem row086_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 57) w=row086 w := by
  have hd : rowDerivative (sourceIndex 57)=(-33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 57)=v 31 := rfl
  have hs : sourceRows 57=[((-1/1:ℚ),8,(-2,0,0,0,0,0,0)),((1/1:ℚ),31,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 57=sourceKind 57 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (57 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row086] <;> ring

theorem row087_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 65) w=row087 w := by
  have hd : rowDerivative (sourceIndex 65)=(-165/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 65)=v 54 := rfl
  have hs : sourceRows 65=[((1/1:ℚ),54,(0,0,0,0,0,0,0)),((1/1:ℚ),64,(0,1,0,0,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 65=sourceKind 65 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (65 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row087] <;> ring

theorem row088_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 66) w=row088 w := by
  have hd : rowDerivative (sourceIndex 66)=(-55/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 66)=v 55 := rfl
  have hs : sourceRows 66=[((1/1:ℚ),0,(-2,-1,0,0,0,1,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 66=sourceKind 66 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (66 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row088] <;> ring

theorem row089_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 67) w=row089 w := by
  have hd : rowDerivative (sourceIndex 67)=(110/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 67)=v 56 := rfl
  have hs : sourceRows 67=[((1/1:ℚ),56,(0,0,0,0,0,0,0)),((1/1:ℚ),63,(2,-1,0,0,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 67=sourceKind 67 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (67 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row089] <;> ring

theorem row090_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 68) w=row090 w := by
  have hd : rowDerivative (sourceIndex 68)=(-66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 68)=v 42 := rfl
  have hs : sourceRows 68=[((1/1:ℚ),13,(2,1,0,0,0,1,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 68=sourceKind 68 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (68 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row090] <;> ring

theorem row091_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 69) w=row091 w := by
  have hd : rowDerivative (sourceIndex 69)=(-33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 69)=v 48 := rfl
  have hs : sourceRows 69=[((1/1:ℚ),14,(0,1,0,0,0,1,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 69=sourceKind 69 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (69 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row091] <;> ring

theorem row092_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 70) w=row092 w := by
  have hd : rowDerivative (sourceIndex 70)=(-22/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 70)=v 50 := rfl
  have hs : sourceRows 70=[((1/1:ℚ),15,(2,-1,0,0,0,1,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 70=sourceKind 70 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (70 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row092] <;> ring

theorem row093_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 71) w=row093 w := by
  have hd : rowDerivative (sourceIndex 71)=(-33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 71)=v 51 := rfl
  have hs : sourceRows 71=[((1/1:ℚ),16,(-2,1,0,0,0,1,0)),((1/1:ℚ),51,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 71=sourceKind 71 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (71 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row093] <;> ring

theorem row094_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 72) w=row094 w := by
  have hd : rowDerivative (sourceIndex 72)=(-11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 72)=v 52 := rfl
  have hs : sourceRows 72=[((1/1:ℚ),18,(0,-1,0,0,0,1,0)),((1/1:ℚ),52,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 72=sourceKind 72 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (72 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row094] <;> ring

theorem row095_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 73) w=row095 w := by
  have hd : rowDerivative (sourceIndex 73)=(-11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 73)=v 53 := rfl
  have hs : sourceRows 73=[((1/1:ℚ),24,(-2,-1,0,0,0,1,0)),((1/1:ℚ),53,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 73=sourceKind 73 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (73 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row095] <;> ring

theorem row096_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 77) w=row096 w := by
  have hd : rowDerivative (sourceIndex 77)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 77)=v 57 := rfl
  have hs : sourceRows 77=[((1/1:ℚ),8,(-2,1,0,0,0,1,0)),((1/1:ℚ),57,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 77=sourceKind 77 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (77 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row096] <;> ring

theorem row097_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 78) w=row097 w := by
  have hd : rowDerivative (sourceIndex 78)=(22/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 78)=v 58 := rfl
  have hs : sourceRows 78=[((1/1:ℚ),9,(2,-1,0,0,0,1,0)),((1/1:ℚ),58,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 78=sourceKind 78 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (78 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row097] <;> ring

theorem row098_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 79) w=row098 w := by
  have hd : rowDerivative (sourceIndex 79)=(33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 79)=v 60 := rfl
  have hs : sourceRows 79=[((1/1:ℚ),10,(0,1,0,0,0,1,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 79=sourceKind 79 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (79 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row098] <;> ring

theorem row099_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 668) w=row099 w := by
  have hd : rowDerivative (sourceIndex 668)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 668)=0 := rfl
  have hs : sourceRows 668=[((1/1:ℚ),22,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 668=sourceKind 668 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (668 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row099] <;> ring

theorem row100_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 669) w=row100 w := by
  have hd : rowDerivative (sourceIndex 669)=(3/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 669)=gridSample 3 (1) v := rfl
  have hs : sourceRows 669=[((1/1:ℚ),0,(-2,0,-1,1,0,1,0)),((1/1:ℚ),23,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(-2,0,-1,1,0,1,0)),((1/1:ℚ),45,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 669=sourceKind 669 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (669 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row100] <;> ring

theorem row101_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 670) w=row101 w := by
  have hd : rowDerivative (sourceIndex 670)=(-3/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 670)=gridSample 3 (-1) v := rfl
  have hs : sourceRows 670=[((1/1:ℚ),0,(-2,0,-1,1,0,1,0)),((1/1:ℚ),21,(0,0,0,0,0,0,0)),((1/1:ℚ),22,(-2,0,-1,1,0,1,0)),((1/1:ℚ),43,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 670=sourceKind 670 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (670 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row101] <;> ring

theorem row102_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 671) w=row102 w := by
  have hd : rowDerivative (sourceIndex 671)=(3/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 671)=gridSample 3 (2) v := rfl
  have hs : sourceRows 671=[((1/1:ℚ),0,(0,0,-1,1,0,1,0)),((1/1:ℚ),22,(0,0,-1,1,0,1,0)),((1/1:ℚ),24,(0,0,0,0,0,0,0)),((1/1:ℚ),46,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 671=sourceKind 671 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (671 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row102] <;> ring

theorem row103_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 672) w=row103 w := by
  have hd : rowDerivative (sourceIndex 672)=(-3/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 672)=gridSample 3 (-2) v := rfl
  have hs : sourceRows 672=[((1/1:ℚ),0,(0,0,-1,1,0,1,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(0,0,-1,1,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 672=sourceKind 672 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (672 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row103] <;> ring

theorem row104_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 673) w=row104 w := by
  have hd : rowDerivative (sourceIndex 673)=(6/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 673)=gridSample 3 (4) v := rfl
  have hs : sourceRows 673=[((1/1:ℚ),11,(2,0,-1,1,0,1,0)),((1/1:ℚ),26,(0,0,0,0,0,0,0)),((1/1:ℚ),33,(2,0,-1,1,0,1,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 673=sourceKind 673 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (673 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row104] <;> ring

theorem row105_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 674) w=row105 w := by
  have hd : rowDerivative (sourceIndex 674)=(-6/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 674)=gridSample 3 (-4) v := rfl
  have hs : sourceRows 674=[((1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),33,(2,0,-1,1,0,1,0)),((1/1:ℚ),40,(0,0,0,0,0,0,0)),((1/1:ℚ),55,(2,0,-1,1,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 674=sourceKind 674 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (674 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row105] <;> ring

theorem row106_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 686) w=row106 w := by
  have hd : rowDerivative (sourceIndex 686)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 686)=0 := rfl
  have hs : sourceRows 686=[((1/1:ℚ),6,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 686=sourceKind 686 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (686 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row106] <;> ring

theorem row107_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 687) w=row107 w := by
  have hd : rowDerivative (sourceIndex 687)=(11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 687)=gridSample 11 (1) v := rfl
  have hs : sourceRows 687=[((1/1:ℚ),0,(-2,-1,0,1,0,0,1)),((1/1:ℚ),6,(-2,-1,0,1,0,0,1)),((1/1:ℚ),7,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(-2,-1,0,1,0,0,1)),((1/1:ℚ),13,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(-2,-1,0,1,0,0,1)),((1/1:ℚ),19,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(-2,-1,0,1,0,0,1)),((1/1:ℚ),25,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(-2,-1,0,1,0,0,1)),((1/1:ℚ),31,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(-2,-1,0,1,0,0,1)),((1/1:ℚ),37,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,-1,0,1,0,0,1)),((1/1:ℚ),43,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(-2,-1,0,1,0,0,1)),((1/1:ℚ),49,(0,0,0,0,0,0,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(-2,-1,0,1,0,0,1)),((1/1:ℚ),61,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 687=sourceKind 687 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (687 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row107] <;> ring

theorem row108_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 688) w=row108 w := by
  have hd : rowDerivative (sourceIndex 688)=(-11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 688)=gridSample 11 (-1) v := rfl
  have hs : sourceRows 688=[((1/1:ℚ),0,(-2,-1,0,1,0,0,1)),((1/1:ℚ),5,(0,0,0,0,0,0,0)),((1/1:ℚ),6,(-2,-1,0,1,0,0,1)),((1/1:ℚ),11,(0,0,0,0,0,0,0)),((1/1:ℚ),17,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(-2,-1,0,1,0,0,1)),((1/1:ℚ),23,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(-2,-1,0,1,0,0,1)),((1/1:ℚ),29,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(-2,-1,0,1,0,0,1)),((1/1:ℚ),35,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(-2,-1,0,1,0,0,1)),((1/1:ℚ),41,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,-1,0,1,0,0,1)),((1/1:ℚ),47,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(-2,-1,0,1,0,0,1)),((1/1:ℚ),53,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(-2,-1,0,1,0,0,1)),((1/1:ℚ),59,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(-2,-1,0,1,0,0,1))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 688=sourceKind 688 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (688 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row108] <;> ring

theorem row109_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 689) w=row109 w := by
  have hd : rowDerivative (sourceIndex 689)=(11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 689)=gridSample 11 (2) v := rfl
  have hs : sourceRows 689=[((1/1:ℚ),0,(0,-1,0,1,0,0,1)),((1/1:ℚ),6,(0,-1,0,1,0,0,1)),((1/1:ℚ),8,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(0,-1,0,1,0,0,1)),((1/1:ℚ),14,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,-1,0,1,0,0,1)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,-1,0,1,0,0,1)),((1/1:ℚ),26,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(0,-1,0,1,0,0,1)),((1/1:ℚ),32,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(0,-1,0,1,0,0,1)),((1/1:ℚ),38,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,-1,0,1,0,0,1)),((1/1:ℚ),44,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(0,-1,0,1,0,0,1)),((1/1:ℚ),50,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(0,-1,0,1,0,0,1)),((1/1:ℚ),56,(0,0,0,0,0,0,0)),((1/1:ℚ),62,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 689=sourceKind 689 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (689 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row109] <;> ring

theorem row110_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 690) w=row110 w := by
  have hd : rowDerivative (sourceIndex 690)=(-11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 690)=gridSample 11 (-2) v := rfl
  have hs : sourceRows 690=[((1/1:ℚ),0,(0,-1,0,1,0,0,1)),((1/1:ℚ),4,(0,0,0,0,0,0,0)),((1/1:ℚ),10,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(0,-1,0,1,0,0,1)),((1/1:ℚ),16,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,-1,0,1,0,0,1)),((1/1:ℚ),22,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,-1,0,1,0,0,1)),((1/1:ℚ),28,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(0,-1,0,1,0,0,1)),((1/1:ℚ),34,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(0,-1,0,1,0,0,1)),((1/1:ℚ),40,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,-1,0,1,0,0,1)),((1/1:ℚ),46,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(0,-1,0,1,0,0,1)),((1/1:ℚ),52,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(0,-1,0,1,0,0,1)),((1/1:ℚ),58,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(0,-1,0,1,0,0,1))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 690=sourceKind 690 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (690 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row110] <;> ring

theorem row111_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 691) w=row111 w := by
  have hd : rowDerivative (sourceIndex 691)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 691)=gridSample 11 (3) v := rfl
  have hs : sourceRows 691=[((1/1:ℚ),2,(-2,1,0,1,0,0,1)),((1/1:ℚ),8,(-2,1,0,1,0,0,1)),((1/1:ℚ),9,(0,0,0,0,0,0,0)),((1/1:ℚ),14,(-2,1,0,1,0,0,1)),((1/1:ℚ),15,(0,0,0,0,0,0,0)),((1/1:ℚ),20,(-2,1,0,1,0,0,1)),((1/1:ℚ),21,(0,0,0,0,0,0,0)),((1/1:ℚ),26,(-2,1,0,1,0,0,1)),((1/1:ℚ),27,(0,0,0,0,0,0,0)),((1/1:ℚ),32,(-2,1,0,1,0,0,1)),((1/1:ℚ),33,(0,0,0,0,0,0,0)),((1/1:ℚ),38,(-2,1,0,1,0,0,1)),((1/1:ℚ),39,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(-2,1,0,1,0,0,1)),((1/1:ℚ),45,(0,0,0,0,0,0,0)),((1/1:ℚ),50,(-2,1,0,1,0,0,1)),((1/1:ℚ),51,(0,0,0,0,0,0,0)),((1/1:ℚ),56,(-2,1,0,1,0,0,1)),((1/1:ℚ),57,(0,0,0,0,0,0,0)),((1/1:ℚ),63,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 691=sourceKind 691 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (691 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row111] <;> ring

theorem row112_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 716) w=row112 w := by
  have hd : rowDerivative (sourceIndex 716)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 716)=0 := rfl
  have hs : sourceRows 716=[((1/1:ℚ),2,(0,0,0,0,0,0,0)),((-1/1:ℚ),4,(-1,0,0,0,1,0,0)),((1/1:ℚ),8,(-2,0,0,0,0,0,0)),((1/1:ℚ),35,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 716=sourceKind 716 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (716 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row112] <;> ring

theorem row113_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 717) w=row113 w := by
  have hd : rowDerivative (sourceIndex 717)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 717)=0 := rfl
  have hs : sourceRows 717=[((1/1:ℚ),3,(0,0,0,0,0,0,0)),((-1/1:ℚ),6,(-1,0,0,0,1,0,0)),((1/1:ℚ),12,(-2,0,0,0,0,0,0)),((1/1:ℚ),36,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 717=sourceKind 717 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (717 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row113] <;> ring

theorem row114_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 718) w=row114 w := by
  have hd : rowDerivative (sourceIndex 718)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 718)=0 := rfl
  have hs : sourceRows 718=[((1/1:ℚ),4,(0,0,0,0,0,0,0)),((-1/1:ℚ),8,(-1,0,0,0,1,0,0)),((1/1:ℚ),16,(-2,0,0,0,0,0,0)),((1/1:ℚ),37,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 718=sourceKind 718 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (718 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row114] <;> ring

theorem row115_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 719) w=row115 w := by
  have hd : rowDerivative (sourceIndex 719)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 719)=0 := rfl
  have hs : sourceRows 719=[((1/1:ℚ),5,(0,0,0,0,0,0,0)),((-1/1:ℚ),10,(-1,0,0,0,1,0,0)),((1/1:ℚ),20,(-2,0,0,0,0,0,0)),((1/1:ℚ),38,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 719=sourceKind 719 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (719 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row115] <;> ring

theorem row116_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 720) w=row116 w := by
  have hd : rowDerivative (sourceIndex 720)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 720)=0 := rfl
  have hs : sourceRows 720=[((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),12,(-1,0,0,0,1,0,0)),((1/1:ℚ),24,(-2,0,0,0,0,0,0)),((1/1:ℚ),39,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 720=sourceKind 720 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (720 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row116] <;> ring

theorem row117_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 721) w=row117 w := by
  have hd : rowDerivative (sourceIndex 721)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 721)=0 := rfl
  have hs : sourceRows 721=[((1/1:ℚ),7,(0,0,0,0,0,0,0)),((-1/1:ℚ),14,(-1,0,0,0,1,0,0)),((1/1:ℚ),28,(-2,0,0,0,0,0,0)),((1/1:ℚ),40,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 721=sourceKind 721 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (721 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row117] <;> ring

theorem row118_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 722) w=row118 w := by
  have hd : rowDerivative (sourceIndex 722)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 722)=0 := rfl
  have hs : sourceRows 722=[((1/1:ℚ),8,(0,0,0,0,0,0,0)),((-1/1:ℚ),16,(-1,0,0,0,1,0,0)),((1/1:ℚ),32,(-2,0,0,0,0,0,0)),((1/1:ℚ),41,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 722=sourceKind 722 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (722 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row118] <;> ring

theorem row119_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 723) w=row119 w := by
  have hd : rowDerivative (sourceIndex 723)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 723)=0 := rfl
  have hs : sourceRows 723=[((1/1:ℚ),9,(0,0,0,0,0,0,0)),((-1/1:ℚ),18,(-1,0,0,0,1,0,0)),((1/1:ℚ),36,(-2,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 723=sourceKind 723 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (723 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row119] <;> ring

theorem row120_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 724) w=row120 w := by
  have hd : rowDerivative (sourceIndex 724)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 724)=0 := rfl
  have hs : sourceRows 724=[((1/1:ℚ),10,(0,0,0,0,0,0,0)),((-1/1:ℚ),20,(-1,0,0,0,1,0,0)),((1/1:ℚ),40,(-2,0,0,0,0,0,0)),((1/1:ℚ),43,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 724=sourceKind 724 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (724 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row120] <;> ring

theorem row121_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 726) w=row121 w := by
  have hd : rowDerivative (sourceIndex 726)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 726)=0 := rfl
  have hs : sourceRows 726=[((1/1:ℚ),12,(0,0,0,0,0,0,0)),((-1/1:ℚ),24,(-1,0,0,0,1,0,0)),((1/1:ℚ),45,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 726=sourceKind 726 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (726 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row121] <;> ring

theorem row122_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 727) w=row122 w := by
  have hd : rowDerivative (sourceIndex 727)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 727)=0 := rfl
  have hs : sourceRows 727=[((1/1:ℚ),13,(0,0,0,0,0,0,0)),((-1/1:ℚ),26,(-1,0,0,0,1,0,0)),((1/1:ℚ),46,(0,0,0,0,0,0,0)),((1/1:ℚ),52,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 727=sourceKind 727 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (727 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row122] <;> ring

theorem row123_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 728) w=row123 w := by
  have hd : rowDerivative (sourceIndex 728)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 728)=0 := rfl
  have hs : sourceRows 728=[((1/1:ℚ),14,(0,0,0,0,0,0,0)),((-1/1:ℚ),28,(-1,0,0,0,1,0,0)),((1/1:ℚ),47,(0,0,0,0,0,0,0)),((1/1:ℚ),56,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 728=sourceKind 728 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (728 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row123] <;> ring

theorem row124_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 729) w=row124 w := by
  have hd : rowDerivative (sourceIndex 729)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 729)=0 := rfl
  have hs : sourceRows 729=[((1/1:ℚ),15,(0,0,0,0,0,0,0)),((-1/1:ℚ),30,(-1,0,0,0,1,0,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 729=sourceKind 729 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (729 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row124] <;> ring

theorem row125_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 730) w=row125 w := by
  have hd : rowDerivative (sourceIndex 730)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 730)=0 := rfl
  have hs : sourceRows 730=[((1/1:ℚ),16,(0,0,0,0,0,0,0)),((-1/1:ℚ),32,(-1,0,0,0,1,0,0)),((1/1:ℚ),49,(0,0,0,0,0,0,0)),((1/1:ℚ),64,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 730=sourceKind 730 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (730 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row125] <;> ring

theorem row126_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 731) w=row126 w := by
  have hd : rowDerivative (sourceIndex 731)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 731)=0 := rfl
  have hs : sourceRows 731=[((1/1:ℚ),2,(-2,0,0,0,0,0,0)),((1/1:ℚ),17,(0,0,0,0,0,0,0)),((-1/1:ℚ),34,(-1,0,0,0,1,0,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 731=sourceKind 731 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (731 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row126] <;> ring

theorem row127_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 732) w=row127 w := by
  have hd : rowDerivative (sourceIndex 732)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 732)=0 := rfl
  have hs : sourceRows 732=[((1/1:ℚ),6,(-2,0,0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,0,0,0)),((-1/1:ℚ),36,(-1,0,0,0,1,0,0)),((1/1:ℚ),51,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 732=sourceKind 732 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (732 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row127] <;> ring

theorem row128_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 733) w=row128 w := by
  have hd : rowDerivative (sourceIndex 733)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 733)=0 := rfl
  have hs : sourceRows 733=[((1/1:ℚ),10,(-2,0,0,0,0,0,0)),((1/1:ℚ),19,(0,0,0,0,0,0,0)),((-1/1:ℚ),38,(-1,0,0,0,1,0,0)),((1/1:ℚ),52,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 733=sourceKind 733 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (733 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row128] <;> ring

theorem row129_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 734) w=row129 w := by
  have hd : rowDerivative (sourceIndex 734)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 734)=0 := rfl
  have hs : sourceRows 734=[((1/1:ℚ),14,(-2,0,0,0,0,0,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((-1/1:ℚ),40,(-1,0,0,0,1,0,0)),((1/1:ℚ),53,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 734=sourceKind 734 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (734 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row129] <;> ring

theorem row130_link (w : Fin 264→ℂ) :
    jetBlockRow 1 (sourceIndex 740) w=row130 w := by
  have hd : rowDerivative (sourceIndex 740)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 740)=0 := rfl
  have hs : sourceRows 740=[((1/1:ℚ),26,(0,0,0,0,0,0,0)),((1/1:ℚ),38,(-2,0,0,0,0,0,0)),((-1/1:ℚ),52,(-1,0,0,0,1,0,0)),((1/1:ℚ),59,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 740=sourceKind 740 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (740 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row130] <;> ring

theorem row131_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 0) w=row131 w := by
  have hd : rowDerivative (sourceIndex 0)=(66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 0)=v 0 := rfl
  have hs : sourceRows 0=[((1/1:ℚ),0,(0,0,0,0,0,0,0)),((-1/1:ℚ),65,(2,1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 0=sourceKind 0 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (0 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row131] <;> ring

theorem row132_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 1) w=row132 w := by
  have hd : rowDerivative (sourceIndex 1)=(33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 1)=v 0 := rfl
  have hs : sourceRows 1=[((1/1:ℚ),0,(0,0,0,0,0,0,0)),((-1/1:ℚ),64,(0,1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 1=sourceKind 1 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (1 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row132] <;> ring

theorem row133_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 2) w=row133 w := by
  have hd : rowDerivative (sourceIndex 2)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 2)=0 := rfl
  have hs : sourceRows 2=[((1/1:ℚ),0,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 2=sourceKind 2 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (2 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row133] <;> ring

theorem row134_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 3) w=row134 w := by
  have hd : rowDerivative (sourceIndex 3)=(1/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 3)=v 1 := rfl
  have hs : sourceRows 3=[((-1/1:ℚ),0,(-2,-1,-1,1,0,0,0)),((1/1:ℚ),1,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 3=sourceKind 3 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (3 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row134] <;> ring

theorem row135_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 4) w=row135 w := by
  have hd : rowDerivative (sourceIndex 4)=(1/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 4)=v 2 := rfl
  have hs : sourceRows 4=[((-1/1:ℚ),0,(0,-1,-1,1,0,0,0)),((1/1:ℚ),2,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 4=sourceKind 4 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (4 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row135] <;> ring

theorem row136_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 5) w=row136 w := by
  have hd : rowDerivative (sourceIndex 5)=(3/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 5)=v 3 := rfl
  have hs : sourceRows 5=[((1/1:ℚ),3,(0,0,0,0,0,0,0)),((-1/1:ℚ),22,(-2,1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 5=sourceKind 5 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (5 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row136] <;> ring

theorem row137_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 6) w=row137 w := by
  have hd : rowDerivative (sourceIndex 6)=(2/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 6)=v 4 := rfl
  have hs : sourceRows 6=[((1/1:ℚ),4,(0,0,0,0,0,0,0)),((-1/1:ℚ),33,(2,-1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 6=sourceKind 6 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (6 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row137] <;> ring

theorem row138_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 7) w=row138 w := by
  have hd : rowDerivative (sourceIndex 7)=(3/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 7)=v 6 := rfl
  have hs : sourceRows 7=[((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),44,(0,1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 7=sourceKind 7 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (7 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row138] <;> ring

theorem row139_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 8) w=row139 w := by
  have hd : rowDerivative (sourceIndex 8)=(11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 8)=v 11 := rfl
  have hs : sourceRows 8=[((1/1:ℚ),11,(0,0,0,0,0,0,0)),((-1/1:ℚ),54,(-2,-1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 8=sourceKind 8 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (8 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row139] <;> ring

theorem row140_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 9) w=row140 w := by
  have hd : rowDerivative (sourceIndex 9)=(6/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 9)=v 12 := rfl
  have hs : sourceRows 9=[((1/1:ℚ),12,(0,0,0,0,0,0,0)),((-1/1:ℚ),55,(2,1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 9=sourceKind 9 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (9 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row140] <;> ring

theorem row141_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 10) w=row141 w := by
  have hd : rowDerivative (sourceIndex 10)=(11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 10)=v 22 := rfl
  have hs : sourceRows 10=[((1/1:ℚ),22,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(0,-1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 10=sourceKind 10 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (10 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row141] <;> ring

theorem row142_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 11) w=row142 w := by
  have hd : rowDerivative (sourceIndex 11)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 11)=v 33 := rfl
  have hs : sourceRows 11=[((1/1:ℚ),33,(0,0,0,0,0,0,0)),((-1/1:ℚ),62,(-2,1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 11=sourceKind 11 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (11 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row142] <;> ring

theorem row143_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 12) w=row143 w := by
  have hd : rowDerivative (sourceIndex 12)=(22/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 12)=v 44 := rfl
  have hs : sourceRows 12=[((1/1:ℚ),44,(0,0,0,0,0,0,0)),((-1/1:ℚ),63,(2,-1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 12=sourceKind 12 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (12 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row143] <;> ring

theorem row144_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 43) w=row144 w := by
  have hd : rowDerivative (sourceIndex 43)=(-165/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 43)=v 33 := rfl
  have hs : sourceRows 43=[((-1/1:ℚ),0,(-2,0,0,0,0,0,0)),((1/1:ℚ),33,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 43=sourceKind 43 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (43 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row144] <;> ring

theorem row145_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 44) w=row145 w := by
  have hd : rowDerivative (sourceIndex 44)=(330/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 44)=v 34 := rfl
  have hs : sourceRows 44=[((1/1:ℚ),34,(0,0,0,0,0,0,0)),((-1/1:ℚ),65,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 44=sourceKind 44 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (44 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row145] <;> ring

theorem row146_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 45) w=row146 w := by
  have hd : rowDerivative (sourceIndex 45)=(-198/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 45)=v 32 := rfl
  have hs : sourceRows 45=[((1/1:ℚ),32,(0,0,0,0,0,0,0)),((-1/1:ℚ),65,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 45=sourceKind 45 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (45 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row146] <;> ring

theorem row147_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 48) w=row147 w := by
  have hd : rowDerivative (sourceIndex 48)=(-66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 48)=v 30 := rfl
  have hs : sourceRows 48=[((1/1:ℚ),30,(0,0,0,0,0,0,0)),((-1/1:ℚ),63,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 48=sourceKind 48 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (48 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row147] <;> ring

theorem row148_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 52) w=row148 w := by
  have hd : rowDerivative (sourceIndex 52)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 52)=v 35 := rfl
  have hs : sourceRows 52=[((1/1:ℚ),35,(0,0,0,0,0,0,0)),((-1/1:ℚ),58,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 52=sourceKind 52 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (52 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row148] <;> ring

theorem row149_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 53) w=row149 w := by
  have hd : rowDerivative (sourceIndex 53)=(33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 53)=v 36 := rfl
  have hs : sourceRows 53=[((1/1:ℚ),36,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 53=sourceKind 53 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (53 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row149] <;> ring

theorem row150_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 54) w=row150 w := by
  have hd : rowDerivative (sourceIndex 54)=(66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 54)=v 38 := rfl
  have hs : sourceRows 54=[((1/1:ℚ),38,(0,0,0,0,0,0,0)),((-1/1:ℚ),61,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 54=sourceKind 54 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (54 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row150] <;> ring

theorem row151_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 55) w=row151 w := by
  have hd : rowDerivative (sourceIndex 55)=(-66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 55)=v 28 := rfl
  have hs : sourceRows 55=[((-1/1:ℚ),5,(2,0,0,0,0,0,0)),((1/1:ℚ),28,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 55=sourceKind 55 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (55 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row151] <;> ring

theorem row152_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 57) w=row152 w := by
  have hd : rowDerivative (sourceIndex 57)=(-33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 57)=v 31 := rfl
  have hs : sourceRows 57=[((-1/1:ℚ),8,(-2,0,0,0,0,0,0)),((1/1:ℚ),31,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 57=sourceKind 57 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (57 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row152] <;> ring

theorem row153_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 65) w=row153 w := by
  have hd : rowDerivative (sourceIndex 65)=(-165/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 65)=v 54 := rfl
  have hs : sourceRows 65=[((1/1:ℚ),54,(0,0,0,0,0,0,0)),((1/1:ℚ),64,(0,1,0,0,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 65=sourceKind 65 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (65 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row153] <;> ring

theorem row154_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 66) w=row154 w := by
  have hd : rowDerivative (sourceIndex 66)=(-55/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 66)=v 55 := rfl
  have hs : sourceRows 66=[((1/1:ℚ),0,(-2,-1,0,0,0,1,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 66=sourceKind 66 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (66 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row154] <;> ring

theorem row155_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 67) w=row155 w := by
  have hd : rowDerivative (sourceIndex 67)=(110/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 67)=v 56 := rfl
  have hs : sourceRows 67=[((1/1:ℚ),56,(0,0,0,0,0,0,0)),((1/1:ℚ),63,(2,-1,0,0,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 67=sourceKind 67 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (67 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row155] <;> ring

theorem row156_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 68) w=row156 w := by
  have hd : rowDerivative (sourceIndex 68)=(-66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 68)=v 42 := rfl
  have hs : sourceRows 68=[((1/1:ℚ),13,(2,1,0,0,0,1,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 68=sourceKind 68 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (68 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row156] <;> ring

theorem row157_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 69) w=row157 w := by
  have hd : rowDerivative (sourceIndex 69)=(-33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 69)=v 48 := rfl
  have hs : sourceRows 69=[((1/1:ℚ),14,(0,1,0,0,0,1,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 69=sourceKind 69 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (69 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row157] <;> ring

theorem row158_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 70) w=row158 w := by
  have hd : rowDerivative (sourceIndex 70)=(-22/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 70)=v 50 := rfl
  have hs : sourceRows 70=[((1/1:ℚ),15,(2,-1,0,0,0,1,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 70=sourceKind 70 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (70 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row158] <;> ring

theorem row159_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 71) w=row159 w := by
  have hd : rowDerivative (sourceIndex 71)=(-33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 71)=v 51 := rfl
  have hs : sourceRows 71=[((1/1:ℚ),16,(-2,1,0,0,0,1,0)),((1/1:ℚ),51,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 71=sourceKind 71 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (71 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row159] <;> ring

theorem row160_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 72) w=row160 w := by
  have hd : rowDerivative (sourceIndex 72)=(-11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 72)=v 52 := rfl
  have hs : sourceRows 72=[((1/1:ℚ),18,(0,-1,0,0,0,1,0)),((1/1:ℚ),52,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 72=sourceKind 72 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (72 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row160] <;> ring

theorem row161_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 73) w=row161 w := by
  have hd : rowDerivative (sourceIndex 73)=(-11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 73)=v 53 := rfl
  have hs : sourceRows 73=[((1/1:ℚ),24,(-2,-1,0,0,0,1,0)),((1/1:ℚ),53,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 73=sourceKind 73 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (73 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row161] <;> ring

theorem row162_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 77) w=row162 w := by
  have hd : rowDerivative (sourceIndex 77)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 77)=v 57 := rfl
  have hs : sourceRows 77=[((1/1:ℚ),8,(-2,1,0,0,0,1,0)),((1/1:ℚ),57,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 77=sourceKind 77 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (77 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row162] <;> ring

theorem row163_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 78) w=row163 w := by
  have hd : rowDerivative (sourceIndex 78)=(22/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 78)=v 58 := rfl
  have hs : sourceRows 78=[((1/1:ℚ),9,(2,-1,0,0,0,1,0)),((1/1:ℚ),58,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 78=sourceKind 78 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (78 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row163] <;> ring

theorem row164_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 79) w=row164 w := by
  have hd : rowDerivative (sourceIndex 79)=(33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 79)=v 60 := rfl
  have hs : sourceRows 79=[((1/1:ℚ),10,(0,1,0,0,0,1,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 79=sourceKind 79 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (79 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row164] <;> ring

theorem row165_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 668) w=row165 w := by
  have hd : rowDerivative (sourceIndex 668)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 668)=0 := rfl
  have hs : sourceRows 668=[((1/1:ℚ),22,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 668=sourceKind 668 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (668 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row165] <;> ring

theorem row166_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 669) w=row166 w := by
  have hd : rowDerivative (sourceIndex 669)=(3/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 669)=gridSample 3 (1) v := rfl
  have hs : sourceRows 669=[((1/1:ℚ),0,(-2,0,-1,1,0,1,0)),((1/1:ℚ),23,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(-2,0,-1,1,0,1,0)),((1/1:ℚ),45,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 669=sourceKind 669 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (669 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row166] <;> ring

theorem row167_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 670) w=row167 w := by
  have hd : rowDerivative (sourceIndex 670)=(-3/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 670)=gridSample 3 (-1) v := rfl
  have hs : sourceRows 670=[((1/1:ℚ),0,(-2,0,-1,1,0,1,0)),((1/1:ℚ),21,(0,0,0,0,0,0,0)),((1/1:ℚ),22,(-2,0,-1,1,0,1,0)),((1/1:ℚ),43,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 670=sourceKind 670 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (670 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row167] <;> ring

theorem row168_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 671) w=row168 w := by
  have hd : rowDerivative (sourceIndex 671)=(3/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 671)=gridSample 3 (2) v := rfl
  have hs : sourceRows 671=[((1/1:ℚ),0,(0,0,-1,1,0,1,0)),((1/1:ℚ),22,(0,0,-1,1,0,1,0)),((1/1:ℚ),24,(0,0,0,0,0,0,0)),((1/1:ℚ),46,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 671=sourceKind 671 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (671 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row168] <;> ring

theorem row169_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 672) w=row169 w := by
  have hd : rowDerivative (sourceIndex 672)=(-3/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 672)=gridSample 3 (-2) v := rfl
  have hs : sourceRows 672=[((1/1:ℚ),0,(0,0,-1,1,0,1,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(0,0,-1,1,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 672=sourceKind 672 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (672 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row169] <;> ring

theorem row170_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 673) w=row170 w := by
  have hd : rowDerivative (sourceIndex 673)=(6/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 673)=gridSample 3 (4) v := rfl
  have hs : sourceRows 673=[((1/1:ℚ),11,(2,0,-1,1,0,1,0)),((1/1:ℚ),26,(0,0,0,0,0,0,0)),((1/1:ℚ),33,(2,0,-1,1,0,1,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 673=sourceKind 673 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (673 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row170] <;> ring

theorem row171_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 674) w=row171 w := by
  have hd : rowDerivative (sourceIndex 674)=(-6/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 674)=gridSample 3 (-4) v := rfl
  have hs : sourceRows 674=[((1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),33,(2,0,-1,1,0,1,0)),((1/1:ℚ),40,(0,0,0,0,0,0,0)),((1/1:ℚ),55,(2,0,-1,1,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 674=sourceKind 674 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (674 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row171] <;> ring

theorem row172_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 686) w=row172 w := by
  have hd : rowDerivative (sourceIndex 686)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 686)=0 := rfl
  have hs : sourceRows 686=[((1/1:ℚ),6,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 686=sourceKind 686 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (686 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row172] <;> ring

theorem row173_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 687) w=row173 w := by
  have hd : rowDerivative (sourceIndex 687)=(11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 687)=gridSample 11 (1) v := rfl
  have hs : sourceRows 687=[((1/1:ℚ),0,(-2,-1,0,1,0,0,1)),((1/1:ℚ),6,(-2,-1,0,1,0,0,1)),((1/1:ℚ),7,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(-2,-1,0,1,0,0,1)),((1/1:ℚ),13,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(-2,-1,0,1,0,0,1)),((1/1:ℚ),19,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(-2,-1,0,1,0,0,1)),((1/1:ℚ),25,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(-2,-1,0,1,0,0,1)),((1/1:ℚ),31,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(-2,-1,0,1,0,0,1)),((1/1:ℚ),37,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,-1,0,1,0,0,1)),((1/1:ℚ),43,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(-2,-1,0,1,0,0,1)),((1/1:ℚ),49,(0,0,0,0,0,0,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(-2,-1,0,1,0,0,1)),((1/1:ℚ),61,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 687=sourceKind 687 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (687 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row173] <;> ring

theorem row174_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 688) w=row174 w := by
  have hd : rowDerivative (sourceIndex 688)=(-11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 688)=gridSample 11 (-1) v := rfl
  have hs : sourceRows 688=[((1/1:ℚ),0,(-2,-1,0,1,0,0,1)),((1/1:ℚ),5,(0,0,0,0,0,0,0)),((1/1:ℚ),6,(-2,-1,0,1,0,0,1)),((1/1:ℚ),11,(0,0,0,0,0,0,0)),((1/1:ℚ),17,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(-2,-1,0,1,0,0,1)),((1/1:ℚ),23,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(-2,-1,0,1,0,0,1)),((1/1:ℚ),29,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(-2,-1,0,1,0,0,1)),((1/1:ℚ),35,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(-2,-1,0,1,0,0,1)),((1/1:ℚ),41,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,-1,0,1,0,0,1)),((1/1:ℚ),47,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(-2,-1,0,1,0,0,1)),((1/1:ℚ),53,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(-2,-1,0,1,0,0,1)),((1/1:ℚ),59,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(-2,-1,0,1,0,0,1))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 688=sourceKind 688 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (688 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row174] <;> ring

theorem row175_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 689) w=row175 w := by
  have hd : rowDerivative (sourceIndex 689)=(11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 689)=gridSample 11 (2) v := rfl
  have hs : sourceRows 689=[((1/1:ℚ),0,(0,-1,0,1,0,0,1)),((1/1:ℚ),6,(0,-1,0,1,0,0,1)),((1/1:ℚ),8,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(0,-1,0,1,0,0,1)),((1/1:ℚ),14,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,-1,0,1,0,0,1)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,-1,0,1,0,0,1)),((1/1:ℚ),26,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(0,-1,0,1,0,0,1)),((1/1:ℚ),32,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(0,-1,0,1,0,0,1)),((1/1:ℚ),38,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,-1,0,1,0,0,1)),((1/1:ℚ),44,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(0,-1,0,1,0,0,1)),((1/1:ℚ),50,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(0,-1,0,1,0,0,1)),((1/1:ℚ),56,(0,0,0,0,0,0,0)),((1/1:ℚ),62,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 689=sourceKind 689 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (689 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row175] <;> ring

theorem row176_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 690) w=row176 w := by
  have hd : rowDerivative (sourceIndex 690)=(-11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 690)=gridSample 11 (-2) v := rfl
  have hs : sourceRows 690=[((1/1:ℚ),0,(0,-1,0,1,0,0,1)),((1/1:ℚ),4,(0,0,0,0,0,0,0)),((1/1:ℚ),10,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(0,-1,0,1,0,0,1)),((1/1:ℚ),16,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,-1,0,1,0,0,1)),((1/1:ℚ),22,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,-1,0,1,0,0,1)),((1/1:ℚ),28,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(0,-1,0,1,0,0,1)),((1/1:ℚ),34,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(0,-1,0,1,0,0,1)),((1/1:ℚ),40,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,-1,0,1,0,0,1)),((1/1:ℚ),46,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(0,-1,0,1,0,0,1)),((1/1:ℚ),52,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(0,-1,0,1,0,0,1)),((1/1:ℚ),58,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(0,-1,0,1,0,0,1))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 690=sourceKind 690 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (690 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row176] <;> ring

theorem row177_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 691) w=row177 w := by
  have hd : rowDerivative (sourceIndex 691)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 691)=gridSample 11 (3) v := rfl
  have hs : sourceRows 691=[((1/1:ℚ),2,(-2,1,0,1,0,0,1)),((1/1:ℚ),8,(-2,1,0,1,0,0,1)),((1/1:ℚ),9,(0,0,0,0,0,0,0)),((1/1:ℚ),14,(-2,1,0,1,0,0,1)),((1/1:ℚ),15,(0,0,0,0,0,0,0)),((1/1:ℚ),20,(-2,1,0,1,0,0,1)),((1/1:ℚ),21,(0,0,0,0,0,0,0)),((1/1:ℚ),26,(-2,1,0,1,0,0,1)),((1/1:ℚ),27,(0,0,0,0,0,0,0)),((1/1:ℚ),32,(-2,1,0,1,0,0,1)),((1/1:ℚ),33,(0,0,0,0,0,0,0)),((1/1:ℚ),38,(-2,1,0,1,0,0,1)),((1/1:ℚ),39,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(-2,1,0,1,0,0,1)),((1/1:ℚ),45,(0,0,0,0,0,0,0)),((1/1:ℚ),50,(-2,1,0,1,0,0,1)),((1/1:ℚ),51,(0,0,0,0,0,0,0)),((1/1:ℚ),56,(-2,1,0,1,0,0,1)),((1/1:ℚ),57,(0,0,0,0,0,0,0)),((1/1:ℚ),63,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 691=sourceKind 691 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (691 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row177] <;> ring

theorem row178_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 716) w=row178 w := by
  have hd : rowDerivative (sourceIndex 716)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 716)=0 := rfl
  have hs : sourceRows 716=[((1/1:ℚ),2,(0,0,0,0,0,0,0)),((-1/1:ℚ),4,(-1,0,0,0,1,0,0)),((1/1:ℚ),8,(-2,0,0,0,0,0,0)),((1/1:ℚ),35,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 716=sourceKind 716 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (716 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row178] <;> ring

theorem row179_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 718) w=row179 w := by
  have hd : rowDerivative (sourceIndex 718)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 718)=0 := rfl
  have hs : sourceRows 718=[((1/1:ℚ),4,(0,0,0,0,0,0,0)),((-1/1:ℚ),8,(-1,0,0,0,1,0,0)),((1/1:ℚ),16,(-2,0,0,0,0,0,0)),((1/1:ℚ),37,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 718=sourceKind 718 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (718 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row179] <;> ring

theorem row180_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 719) w=row180 w := by
  have hd : rowDerivative (sourceIndex 719)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 719)=0 := rfl
  have hs : sourceRows 719=[((1/1:ℚ),5,(0,0,0,0,0,0,0)),((-1/1:ℚ),10,(-1,0,0,0,1,0,0)),((1/1:ℚ),20,(-2,0,0,0,0,0,0)),((1/1:ℚ),38,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 719=sourceKind 719 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (719 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row180] <;> ring

theorem row181_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 720) w=row181 w := by
  have hd : rowDerivative (sourceIndex 720)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 720)=0 := rfl
  have hs : sourceRows 720=[((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),12,(-1,0,0,0,1,0,0)),((1/1:ℚ),24,(-2,0,0,0,0,0,0)),((1/1:ℚ),39,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 720=sourceKind 720 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (720 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row181] <;> ring

theorem row182_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 721) w=row182 w := by
  have hd : rowDerivative (sourceIndex 721)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 721)=0 := rfl
  have hs : sourceRows 721=[((1/1:ℚ),7,(0,0,0,0,0,0,0)),((-1/1:ℚ),14,(-1,0,0,0,1,0,0)),((1/1:ℚ),28,(-2,0,0,0,0,0,0)),((1/1:ℚ),40,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 721=sourceKind 721 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (721 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row182] <;> ring

theorem row183_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 722) w=row183 w := by
  have hd : rowDerivative (sourceIndex 722)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 722)=0 := rfl
  have hs : sourceRows 722=[((1/1:ℚ),8,(0,0,0,0,0,0,0)),((-1/1:ℚ),16,(-1,0,0,0,1,0,0)),((1/1:ℚ),32,(-2,0,0,0,0,0,0)),((1/1:ℚ),41,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 722=sourceKind 722 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (722 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row183] <;> ring

theorem row184_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 723) w=row184 w := by
  have hd : rowDerivative (sourceIndex 723)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 723)=0 := rfl
  have hs : sourceRows 723=[((1/1:ℚ),9,(0,0,0,0,0,0,0)),((-1/1:ℚ),18,(-1,0,0,0,1,0,0)),((1/1:ℚ),36,(-2,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 723=sourceKind 723 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (723 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row184] <;> ring

theorem row185_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 724) w=row185 w := by
  have hd : rowDerivative (sourceIndex 724)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 724)=0 := rfl
  have hs : sourceRows 724=[((1/1:ℚ),10,(0,0,0,0,0,0,0)),((-1/1:ℚ),20,(-1,0,0,0,1,0,0)),((1/1:ℚ),40,(-2,0,0,0,0,0,0)),((1/1:ℚ),43,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 724=sourceKind 724 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (724 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row185] <;> ring

theorem row186_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 726) w=row186 w := by
  have hd : rowDerivative (sourceIndex 726)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 726)=0 := rfl
  have hs : sourceRows 726=[((1/1:ℚ),12,(0,0,0,0,0,0,0)),((-1/1:ℚ),24,(-1,0,0,0,1,0,0)),((1/1:ℚ),45,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 726=sourceKind 726 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (726 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row186] <;> ring

theorem row187_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 727) w=row187 w := by
  have hd : rowDerivative (sourceIndex 727)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 727)=0 := rfl
  have hs : sourceRows 727=[((1/1:ℚ),13,(0,0,0,0,0,0,0)),((-1/1:ℚ),26,(-1,0,0,0,1,0,0)),((1/1:ℚ),46,(0,0,0,0,0,0,0)),((1/1:ℚ),52,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 727=sourceKind 727 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (727 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row187] <;> ring

theorem row188_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 728) w=row188 w := by
  have hd : rowDerivative (sourceIndex 728)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 728)=0 := rfl
  have hs : sourceRows 728=[((1/1:ℚ),14,(0,0,0,0,0,0,0)),((-1/1:ℚ),28,(-1,0,0,0,1,0,0)),((1/1:ℚ),47,(0,0,0,0,0,0,0)),((1/1:ℚ),56,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 728=sourceKind 728 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (728 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row188] <;> ring

theorem row189_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 729) w=row189 w := by
  have hd : rowDerivative (sourceIndex 729)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 729)=0 := rfl
  have hs : sourceRows 729=[((1/1:ℚ),15,(0,0,0,0,0,0,0)),((-1/1:ℚ),30,(-1,0,0,0,1,0,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 729=sourceKind 729 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (729 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row189] <;> ring

theorem row190_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 730) w=row190 w := by
  have hd : rowDerivative (sourceIndex 730)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 730)=0 := rfl
  have hs : sourceRows 730=[((1/1:ℚ),16,(0,0,0,0,0,0,0)),((-1/1:ℚ),32,(-1,0,0,0,1,0,0)),((1/1:ℚ),49,(0,0,0,0,0,0,0)),((1/1:ℚ),64,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 730=sourceKind 730 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (730 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row190] <;> ring

theorem row191_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 731) w=row191 w := by
  have hd : rowDerivative (sourceIndex 731)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 731)=0 := rfl
  have hs : sourceRows 731=[((1/1:ℚ),2,(-2,0,0,0,0,0,0)),((1/1:ℚ),17,(0,0,0,0,0,0,0)),((-1/1:ℚ),34,(-1,0,0,0,1,0,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 731=sourceKind 731 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (731 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row191] <;> ring

theorem row192_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 732) w=row192 w := by
  have hd : rowDerivative (sourceIndex 732)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 732)=0 := rfl
  have hs : sourceRows 732=[((1/1:ℚ),6,(-2,0,0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,0,0,0)),((-1/1:ℚ),36,(-1,0,0,0,1,0,0)),((1/1:ℚ),51,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 732=sourceKind 732 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (732 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row192] <;> ring

theorem row193_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 733) w=row193 w := by
  have hd : rowDerivative (sourceIndex 733)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 733)=0 := rfl
  have hs : sourceRows 733=[((1/1:ℚ),10,(-2,0,0,0,0,0,0)),((1/1:ℚ),19,(0,0,0,0,0,0,0)),((-1/1:ℚ),38,(-1,0,0,0,1,0,0)),((1/1:ℚ),52,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 733=sourceKind 733 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (733 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row193] <;> ring

theorem row194_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 734) w=row194 w := by
  have hd : rowDerivative (sourceIndex 734)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 734)=0 := rfl
  have hs : sourceRows 734=[((1/1:ℚ),14,(-2,0,0,0,0,0,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((-1/1:ℚ),40,(-1,0,0,0,1,0,0)),((1/1:ℚ),53,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 734=sourceKind 734 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (734 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row194] <;> ring

theorem row195_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 740) w=row195 w := by
  have hd : rowDerivative (sourceIndex 740)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 740)=0 := rfl
  have hs : sourceRows 740=[((1/1:ℚ),26,(0,0,0,0,0,0,0)),((1/1:ℚ),38,(-2,0,0,0,0,0,0)),((-1/1:ℚ),52,(-1,0,0,0,1,0,0)),((1/1:ℚ),59,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 740=sourceKind 740 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (740 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row195] <;> ring

theorem row196_link (w : Fin 264→ℂ) :
    jetBlockRow 2 (sourceIndex 750) w=row196 w := by
  have hd : rowDerivative (sourceIndex 750)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 750)=0 := rfl
  have hs : sourceRows 750=[((1/1:ℚ),3,(0,0,0,0,0,0,0)),((-1/1:ℚ),9,(0,-1,0,0,0,1,0)),((1/1:ℚ),25,(0,0,0,0,0,0,0)),((1/1:ℚ),47,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 750=sourceKind 750 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (750 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row196] <;> ring

theorem row197_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 0) w=row197 w := by
  have hd : rowDerivative (sourceIndex 0)=(66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 0)=v 0 := rfl
  have hs : sourceRows 0=[((1/1:ℚ),0,(0,0,0,0,0,0,0)),((-1/1:ℚ),65,(2,1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 0=sourceKind 0 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (0 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row197] <;> ring

theorem row198_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 1) w=row198 w := by
  have hd : rowDerivative (sourceIndex 1)=(33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 1)=v 0 := rfl
  have hs : sourceRows 1=[((1/1:ℚ),0,(0,0,0,0,0,0,0)),((-1/1:ℚ),64,(0,1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 1=sourceKind 1 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (1 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row198] <;> ring

theorem row199_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 2) w=row199 w := by
  have hd : rowDerivative (sourceIndex 2)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 2)=0 := rfl
  have hs : sourceRows 2=[((1/1:ℚ),0,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 2=sourceKind 2 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (2 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row199] <;> ring

theorem row200_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 3) w=row200 w := by
  have hd : rowDerivative (sourceIndex 3)=(1/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 3)=v 1 := rfl
  have hs : sourceRows 3=[((-1/1:ℚ),0,(-2,-1,-1,1,0,0,0)),((1/1:ℚ),1,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 3=sourceKind 3 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (3 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row200] <;> ring

theorem row201_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 4) w=row201 w := by
  have hd : rowDerivative (sourceIndex 4)=(1/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 4)=v 2 := rfl
  have hs : sourceRows 4=[((-1/1:ℚ),0,(0,-1,-1,1,0,0,0)),((1/1:ℚ),2,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 4=sourceKind 4 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (4 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row201] <;> ring

theorem row202_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 5) w=row202 w := by
  have hd : rowDerivative (sourceIndex 5)=(3/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 5)=v 3 := rfl
  have hs : sourceRows 5=[((1/1:ℚ),3,(0,0,0,0,0,0,0)),((-1/1:ℚ),22,(-2,1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 5=sourceKind 5 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (5 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row202] <;> ring

theorem row203_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 6) w=row203 w := by
  have hd : rowDerivative (sourceIndex 6)=(2/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 6)=v 4 := rfl
  have hs : sourceRows 6=[((1/1:ℚ),4,(0,0,0,0,0,0,0)),((-1/1:ℚ),33,(2,-1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 6=sourceKind 6 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (6 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row203] <;> ring

theorem row204_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 7) w=row204 w := by
  have hd : rowDerivative (sourceIndex 7)=(3/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 7)=v 6 := rfl
  have hs : sourceRows 7=[((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),44,(0,1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 7=sourceKind 7 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (7 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row204] <;> ring

theorem row205_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 8) w=row205 w := by
  have hd : rowDerivative (sourceIndex 8)=(11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 8)=v 11 := rfl
  have hs : sourceRows 8=[((1/1:ℚ),11,(0,0,0,0,0,0,0)),((-1/1:ℚ),54,(-2,-1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 8=sourceKind 8 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (8 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row205] <;> ring

theorem row206_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 9) w=row206 w := by
  have hd : rowDerivative (sourceIndex 9)=(6/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 9)=v 12 := rfl
  have hs : sourceRows 9=[((1/1:ℚ),12,(0,0,0,0,0,0,0)),((-1/1:ℚ),55,(2,1,-1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 9=sourceKind 9 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (9 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row206] <;> ring

theorem row207_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 10) w=row207 w := by
  have hd : rowDerivative (sourceIndex 10)=(11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 10)=v 22 := rfl
  have hs : sourceRows 10=[((1/1:ℚ),22,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(0,-1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 10=sourceKind 10 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (10 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row207] <;> ring

theorem row208_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 11) w=row208 w := by
  have hd : rowDerivative (sourceIndex 11)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 11)=v 33 := rfl
  have hs : sourceRows 11=[((1/1:ℚ),33,(0,0,0,0,0,0,0)),((-1/1:ℚ),62,(-2,1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 11=sourceKind 11 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (11 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row208] <;> ring

theorem row209_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 12) w=row209 w := by
  have hd : rowDerivative (sourceIndex 12)=(22/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 12)=v 44 := rfl
  have hs : sourceRows 12=[((1/1:ℚ),44,(0,0,0,0,0,0,0)),((-1/1:ℚ),63,(2,-1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 12=sourceKind 12 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (12 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row209] <;> ring

theorem row210_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 43) w=row210 w := by
  have hd : rowDerivative (sourceIndex 43)=(-165/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 43)=v 33 := rfl
  have hs : sourceRows 43=[((-1/1:ℚ),0,(-2,0,0,0,0,0,0)),((1/1:ℚ),33,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 43=sourceKind 43 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (43 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row210] <;> ring

theorem row211_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 44) w=row211 w := by
  have hd : rowDerivative (sourceIndex 44)=(330/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 44)=v 34 := rfl
  have hs : sourceRows 44=[((1/1:ℚ),34,(0,0,0,0,0,0,0)),((-1/1:ℚ),65,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 44=sourceKind 44 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (44 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row211] <;> ring

theorem row212_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 45) w=row212 w := by
  have hd : rowDerivative (sourceIndex 45)=(-198/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 45)=v 32 := rfl
  have hs : sourceRows 45=[((1/1:ℚ),32,(0,0,0,0,0,0,0)),((-1/1:ℚ),65,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 45=sourceKind 45 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (45 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row212] <;> ring

theorem row213_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 48) w=row213 w := by
  have hd : rowDerivative (sourceIndex 48)=(-66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 48)=v 30 := rfl
  have hs : sourceRows 48=[((1/1:ℚ),30,(0,0,0,0,0,0,0)),((-1/1:ℚ),63,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 48=sourceKind 48 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (48 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row213] <;> ring

theorem row214_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 52) w=row214 w := by
  have hd : rowDerivative (sourceIndex 52)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 52)=v 35 := rfl
  have hs : sourceRows 52=[((1/1:ℚ),35,(0,0,0,0,0,0,0)),((-1/1:ℚ),58,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 52=sourceKind 52 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (52 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row214] <;> ring

theorem row215_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 53) w=row215 w := by
  have hd : rowDerivative (sourceIndex 53)=(33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 53)=v 36 := rfl
  have hs : sourceRows 53=[((1/1:ℚ),36,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 53=sourceKind 53 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (53 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row215] <;> ring

theorem row216_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 54) w=row216 w := by
  have hd : rowDerivative (sourceIndex 54)=(66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 54)=v 38 := rfl
  have hs : sourceRows 54=[((1/1:ℚ),38,(0,0,0,0,0,0,0)),((-1/1:ℚ),61,(2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 54=sourceKind 54 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (54 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row216] <;> ring

theorem row217_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 55) w=row217 w := by
  have hd : rowDerivative (sourceIndex 55)=(-66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 55)=v 28 := rfl
  have hs : sourceRows 55=[((-1/1:ℚ),5,(2,0,0,0,0,0,0)),((1/1:ℚ),28,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 55=sourceKind 55 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (55 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row217] <;> ring

theorem row218_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 57) w=row218 w := by
  have hd : rowDerivative (sourceIndex 57)=(-33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 57)=v 31 := rfl
  have hs : sourceRows 57=[((-1/1:ℚ),8,(-2,0,0,0,0,0,0)),((1/1:ℚ),31,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 57=sourceKind 57 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (57 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row218] <;> ring

theorem row219_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 65) w=row219 w := by
  have hd : rowDerivative (sourceIndex 65)=(-165/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 65)=v 54 := rfl
  have hs : sourceRows 65=[((1/1:ℚ),54,(0,0,0,0,0,0,0)),((1/1:ℚ),64,(0,1,0,0,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 65=sourceKind 65 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (65 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row219] <;> ring

theorem row220_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 66) w=row220 w := by
  have hd : rowDerivative (sourceIndex 66)=(-55/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 66)=v 55 := rfl
  have hs : sourceRows 66=[((1/1:ℚ),0,(-2,-1,0,0,0,1,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 66=sourceKind 66 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (66 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row220] <;> ring

theorem row221_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 67) w=row221 w := by
  have hd : rowDerivative (sourceIndex 67)=(110/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 67)=v 56 := rfl
  have hs : sourceRows 67=[((1/1:ℚ),56,(0,0,0,0,0,0,0)),((1/1:ℚ),63,(2,-1,0,0,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 67=sourceKind 67 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (67 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row221] <;> ring

theorem row222_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 68) w=row222 w := by
  have hd : rowDerivative (sourceIndex 68)=(-66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 68)=v 42 := rfl
  have hs : sourceRows 68=[((1/1:ℚ),13,(2,1,0,0,0,1,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 68=sourceKind 68 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (68 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row222] <;> ring

theorem row223_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 69) w=row223 w := by
  have hd : rowDerivative (sourceIndex 69)=(-33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 69)=v 48 := rfl
  have hs : sourceRows 69=[((1/1:ℚ),14,(0,1,0,0,0,1,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 69=sourceKind 69 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (69 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row223] <;> ring

theorem row224_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 70) w=row224 w := by
  have hd : rowDerivative (sourceIndex 70)=(-22/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 70)=v 50 := rfl
  have hs : sourceRows 70=[((1/1:ℚ),15,(2,-1,0,0,0,1,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 70=sourceKind 70 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (70 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row224] <;> ring

theorem row225_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 71) w=row225 w := by
  have hd : rowDerivative (sourceIndex 71)=(-33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 71)=v 51 := rfl
  have hs : sourceRows 71=[((1/1:ℚ),16,(-2,1,0,0,0,1,0)),((1/1:ℚ),51,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 71=sourceKind 71 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (71 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row225] <;> ring

theorem row226_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 72) w=row226 w := by
  have hd : rowDerivative (sourceIndex 72)=(-11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 72)=v 52 := rfl
  have hs : sourceRows 72=[((1/1:ℚ),18,(0,-1,0,0,0,1,0)),((1/1:ℚ),52,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 72=sourceKind 72 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (72 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row226] <;> ring

theorem row227_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 73) w=row227 w := by
  have hd : rowDerivative (sourceIndex 73)=(-11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 73)=v 53 := rfl
  have hs : sourceRows 73=[((1/1:ℚ),24,(-2,-1,0,0,0,1,0)),((1/1:ℚ),53,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 73=sourceKind 73 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (73 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row227] <;> ring

theorem row228_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 77) w=row228 w := by
  have hd : rowDerivative (sourceIndex 77)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 77)=v 57 := rfl
  have hs : sourceRows 77=[((1/1:ℚ),8,(-2,1,0,0,0,1,0)),((1/1:ℚ),57,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 77=sourceKind 77 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (77 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row228] <;> ring

theorem row229_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 78) w=row229 w := by
  have hd : rowDerivative (sourceIndex 78)=(22/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 78)=v 58 := rfl
  have hs : sourceRows 78=[((1/1:ℚ),9,(2,-1,0,0,0,1,0)),((1/1:ℚ),58,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 78=sourceKind 78 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (78 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row229] <;> ring

theorem row230_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 79) w=row230 w := by
  have hd : rowDerivative (sourceIndex 79)=(33/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 79)=v 60 := rfl
  have hs : sourceRows 79=[((1/1:ℚ),10,(0,1,0,0,0,1,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 79=sourceKind 79 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (79 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row230] <;> ring

theorem row232_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 669) w=row232 w := by
  have hd : rowDerivative (sourceIndex 669)=(3/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 669)=gridSample 3 (1) v := rfl
  have hs : sourceRows 669=[((1/1:ℚ),0,(-2,0,-1,1,0,1,0)),((1/1:ℚ),23,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(-2,0,-1,1,0,1,0)),((1/1:ℚ),45,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 669=sourceKind 669 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (669 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row232] <;> ring

theorem row233_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 670) w=row233 w := by
  have hd : rowDerivative (sourceIndex 670)=(-3/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 670)=gridSample 3 (-1) v := rfl
  have hs : sourceRows 670=[((1/1:ℚ),0,(-2,0,-1,1,0,1,0)),((1/1:ℚ),21,(0,0,0,0,0,0,0)),((1/1:ℚ),22,(-2,0,-1,1,0,1,0)),((1/1:ℚ),43,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 670=sourceKind 670 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (670 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row233] <;> ring

theorem row234_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 671) w=row234 w := by
  have hd : rowDerivative (sourceIndex 671)=(3/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 671)=gridSample 3 (2) v := rfl
  have hs : sourceRows 671=[((1/1:ℚ),0,(0,0,-1,1,0,1,0)),((1/1:ℚ),22,(0,0,-1,1,0,1,0)),((1/1:ℚ),24,(0,0,0,0,0,0,0)),((1/1:ℚ),46,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 671=sourceKind 671 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (671 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row234] <;> ring

theorem row235_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 672) w=row235 w := by
  have hd : rowDerivative (sourceIndex 672)=(-3/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 672)=gridSample 3 (-2) v := rfl
  have hs : sourceRows 672=[((1/1:ℚ),0,(0,0,-1,1,0,1,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(0,0,-1,1,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 672=sourceKind 672 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (672 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row235] <;> ring

theorem row236_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 673) w=row236 w := by
  have hd : rowDerivative (sourceIndex 673)=(6/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 673)=gridSample 3 (4) v := rfl
  have hs : sourceRows 673=[((1/1:ℚ),11,(2,0,-1,1,0,1,0)),((1/1:ℚ),26,(0,0,0,0,0,0,0)),((1/1:ℚ),33,(2,0,-1,1,0,1,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 673=sourceKind 673 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (673 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row236] <;> ring

theorem row237_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 674) w=row237 w := by
  have hd : rowDerivative (sourceIndex 674)=(-6/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 674)=gridSample 3 (-4) v := rfl
  have hs : sourceRows 674=[((1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),33,(2,0,-1,1,0,1,0)),((1/1:ℚ),40,(0,0,0,0,0,0,0)),((1/1:ℚ),55,(2,0,-1,1,0,1,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 674=sourceKind 674 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (674 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row237] <;> ring

theorem row238_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 686) w=row238 w := by
  have hd : rowDerivative (sourceIndex 686)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 686)=0 := rfl
  have hs : sourceRows 686=[((1/1:ℚ),6,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 686=sourceKind 686 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (686 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row238] <;> ring

theorem row239_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 687) w=row239 w := by
  have hd : rowDerivative (sourceIndex 687)=(11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 687)=gridSample 11 (1) v := rfl
  have hs : sourceRows 687=[((1/1:ℚ),0,(-2,-1,0,1,0,0,1)),((1/1:ℚ),6,(-2,-1,0,1,0,0,1)),((1/1:ℚ),7,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(-2,-1,0,1,0,0,1)),((1/1:ℚ),13,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(-2,-1,0,1,0,0,1)),((1/1:ℚ),19,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(-2,-1,0,1,0,0,1)),((1/1:ℚ),25,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(-2,-1,0,1,0,0,1)),((1/1:ℚ),31,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(-2,-1,0,1,0,0,1)),((1/1:ℚ),37,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,-1,0,1,0,0,1)),((1/1:ℚ),43,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(-2,-1,0,1,0,0,1)),((1/1:ℚ),49,(0,0,0,0,0,0,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(-2,-1,0,1,0,0,1)),((1/1:ℚ),61,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 687=sourceKind 687 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (687 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row239] <;> ring

theorem row240_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 688) w=row240 w := by
  have hd : rowDerivative (sourceIndex 688)=(-11/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 688)=gridSample 11 (-1) v := rfl
  have hs : sourceRows 688=[((1/1:ℚ),0,(-2,-1,0,1,0,0,1)),((1/1:ℚ),5,(0,0,0,0,0,0,0)),((1/1:ℚ),6,(-2,-1,0,1,0,0,1)),((1/1:ℚ),11,(0,0,0,0,0,0,0)),((1/1:ℚ),17,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(-2,-1,0,1,0,0,1)),((1/1:ℚ),23,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(-2,-1,0,1,0,0,1)),((1/1:ℚ),29,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(-2,-1,0,1,0,0,1)),((1/1:ℚ),35,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(-2,-1,0,1,0,0,1)),((1/1:ℚ),41,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,-1,0,1,0,0,1)),((1/1:ℚ),47,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(-2,-1,0,1,0,0,1)),((1/1:ℚ),53,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(-2,-1,0,1,0,0,1)),((1/1:ℚ),59,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(-2,-1,0,1,0,0,1))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 688=sourceKind 688 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (688 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row240] <;> ring

theorem row241_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 689) w=row241 w := by
  have hd : rowDerivative (sourceIndex 689)=(11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 689)=gridSample 11 (2) v := rfl
  have hs : sourceRows 689=[((1/1:ℚ),0,(0,-1,0,1,0,0,1)),((1/1:ℚ),6,(0,-1,0,1,0,0,1)),((1/1:ℚ),8,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(0,-1,0,1,0,0,1)),((1/1:ℚ),14,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,-1,0,1,0,0,1)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,-1,0,1,0,0,1)),((1/1:ℚ),26,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(0,-1,0,1,0,0,1)),((1/1:ℚ),32,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(0,-1,0,1,0,0,1)),((1/1:ℚ),38,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,-1,0,1,0,0,1)),((1/1:ℚ),44,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(0,-1,0,1,0,0,1)),((1/1:ℚ),50,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(0,-1,0,1,0,0,1)),((1/1:ℚ),56,(0,0,0,0,0,0,0)),((1/1:ℚ),62,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 689=sourceKind 689 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (689 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row241] <;> ring

theorem row242_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 690) w=row242 w := by
  have hd : rowDerivative (sourceIndex 690)=(-11/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 690)=gridSample 11 (-2) v := rfl
  have hs : sourceRows 690=[((1/1:ℚ),0,(0,-1,0,1,0,0,1)),((1/1:ℚ),4,(0,0,0,0,0,0,0)),((1/1:ℚ),10,(0,0,0,0,0,0,0)),((1/1:ℚ),12,(0,-1,0,1,0,0,1)),((1/1:ℚ),16,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,-1,0,1,0,0,1)),((1/1:ℚ),22,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,-1,0,1,0,0,1)),((1/1:ℚ),28,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(0,-1,0,1,0,0,1)),((1/1:ℚ),34,(0,0,0,0,0,0,0)),((1/1:ℚ),36,(0,-1,0,1,0,0,1)),((1/1:ℚ),40,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,-1,0,1,0,0,1)),((1/1:ℚ),46,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(0,-1,0,1,0,0,1)),((1/1:ℚ),52,(0,0,0,0,0,0,0)),((1/1:ℚ),54,(0,-1,0,1,0,0,1)),((1/1:ℚ),58,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(0,-1,0,1,0,0,1))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 690=sourceKind 690 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (690 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row242] <;> ring

theorem row243_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 691) w=row243 w := by
  have hd : rowDerivative (sourceIndex 691)=(33/2:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 691)=gridSample 11 (3) v := rfl
  have hs : sourceRows 691=[((1/1:ℚ),2,(-2,1,0,1,0,0,1)),((1/1:ℚ),8,(-2,1,0,1,0,0,1)),((1/1:ℚ),9,(0,0,0,0,0,0,0)),((1/1:ℚ),14,(-2,1,0,1,0,0,1)),((1/1:ℚ),15,(0,0,0,0,0,0,0)),((1/1:ℚ),20,(-2,1,0,1,0,0,1)),((1/1:ℚ),21,(0,0,0,0,0,0,0)),((1/1:ℚ),26,(-2,1,0,1,0,0,1)),((1/1:ℚ),27,(0,0,0,0,0,0,0)),((1/1:ℚ),32,(-2,1,0,1,0,0,1)),((1/1:ℚ),33,(0,0,0,0,0,0,0)),((1/1:ℚ),38,(-2,1,0,1,0,0,1)),((1/1:ℚ),39,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(-2,1,0,1,0,0,1)),((1/1:ℚ),45,(0,0,0,0,0,0,0)),((1/1:ℚ),50,(-2,1,0,1,0,0,1)),((1/1:ℚ),51,(0,0,0,0,0,0,0)),((1/1:ℚ),56,(-2,1,0,1,0,0,1)),((1/1:ℚ),57,(0,0,0,0,0,0,0)),((1/1:ℚ),63,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 691=sourceKind 691 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (691 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row243] <;> ring

theorem row244_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 716) w=row244 w := by
  have hd : rowDerivative (sourceIndex 716)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 716)=0 := rfl
  have hs : sourceRows 716=[((1/1:ℚ),2,(0,0,0,0,0,0,0)),((-1/1:ℚ),4,(-1,0,0,0,1,0,0)),((1/1:ℚ),8,(-2,0,0,0,0,0,0)),((1/1:ℚ),35,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 716=sourceKind 716 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (716 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row244] <;> ring

theorem row245_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 717) w=row245 w := by
  have hd : rowDerivative (sourceIndex 717)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 717)=0 := rfl
  have hs : sourceRows 717=[((1/1:ℚ),3,(0,0,0,0,0,0,0)),((-1/1:ℚ),6,(-1,0,0,0,1,0,0)),((1/1:ℚ),12,(-2,0,0,0,0,0,0)),((1/1:ℚ),36,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 717=sourceKind 717 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (717 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row245] <;> ring

theorem row246_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 718) w=row246 w := by
  have hd : rowDerivative (sourceIndex 718)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 718)=0 := rfl
  have hs : sourceRows 718=[((1/1:ℚ),4,(0,0,0,0,0,0,0)),((-1/1:ℚ),8,(-1,0,0,0,1,0,0)),((1/1:ℚ),16,(-2,0,0,0,0,0,0)),((1/1:ℚ),37,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 718=sourceKind 718 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (718 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row246] <;> ring

theorem row247_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 719) w=row247 w := by
  have hd : rowDerivative (sourceIndex 719)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 719)=0 := rfl
  have hs : sourceRows 719=[((1/1:ℚ),5,(0,0,0,0,0,0,0)),((-1/1:ℚ),10,(-1,0,0,0,1,0,0)),((1/1:ℚ),20,(-2,0,0,0,0,0,0)),((1/1:ℚ),38,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 719=sourceKind 719 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (719 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row247] <;> ring

theorem row248_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 720) w=row248 w := by
  have hd : rowDerivative (sourceIndex 720)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 720)=0 := rfl
  have hs : sourceRows 720=[((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),12,(-1,0,0,0,1,0,0)),((1/1:ℚ),24,(-2,0,0,0,0,0,0)),((1/1:ℚ),39,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 720=sourceKind 720 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (720 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row248] <;> ring

theorem row249_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 721) w=row249 w := by
  have hd : rowDerivative (sourceIndex 721)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 721)=0 := rfl
  have hs : sourceRows 721=[((1/1:ℚ),7,(0,0,0,0,0,0,0)),((-1/1:ℚ),14,(-1,0,0,0,1,0,0)),((1/1:ℚ),28,(-2,0,0,0,0,0,0)),((1/1:ℚ),40,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 721=sourceKind 721 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (721 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row249] <;> ring

theorem row250_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 722) w=row250 w := by
  have hd : rowDerivative (sourceIndex 722)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 722)=0 := rfl
  have hs : sourceRows 722=[((1/1:ℚ),8,(0,0,0,0,0,0,0)),((-1/1:ℚ),16,(-1,0,0,0,1,0,0)),((1/1:ℚ),32,(-2,0,0,0,0,0,0)),((1/1:ℚ),41,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 722=sourceKind 722 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (722 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row250] <;> ring

theorem row251_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 723) w=row251 w := by
  have hd : rowDerivative (sourceIndex 723)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 723)=0 := rfl
  have hs : sourceRows 723=[((1/1:ℚ),9,(0,0,0,0,0,0,0)),((-1/1:ℚ),18,(-1,0,0,0,1,0,0)),((1/1:ℚ),36,(-2,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 723=sourceKind 723 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (723 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row251] <;> ring

theorem row252_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 724) w=row252 w := by
  have hd : rowDerivative (sourceIndex 724)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 724)=0 := rfl
  have hs : sourceRows 724=[((1/1:ℚ),10,(0,0,0,0,0,0,0)),((-1/1:ℚ),20,(-1,0,0,0,1,0,0)),((1/1:ℚ),40,(-2,0,0,0,0,0,0)),((1/1:ℚ),43,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 724=sourceKind 724 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (724 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row252] <;> ring

theorem row253_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 726) w=row253 w := by
  have hd : rowDerivative (sourceIndex 726)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 726)=0 := rfl
  have hs : sourceRows 726=[((1/1:ℚ),12,(0,0,0,0,0,0,0)),((-1/1:ℚ),24,(-1,0,0,0,1,0,0)),((1/1:ℚ),45,(0,0,0,0,0,0,0)),((1/1:ℚ),48,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 726=sourceKind 726 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (726 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row253] <;> ring

theorem row254_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 727) w=row254 w := by
  have hd : rowDerivative (sourceIndex 727)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 727)=0 := rfl
  have hs : sourceRows 727=[((1/1:ℚ),13,(0,0,0,0,0,0,0)),((-1/1:ℚ),26,(-1,0,0,0,1,0,0)),((1/1:ℚ),46,(0,0,0,0,0,0,0)),((1/1:ℚ),52,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 727=sourceKind 727 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (727 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row254] <;> ring

theorem row255_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 728) w=row255 w := by
  have hd : rowDerivative (sourceIndex 728)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 728)=0 := rfl
  have hs : sourceRows 728=[((1/1:ℚ),14,(0,0,0,0,0,0,0)),((-1/1:ℚ),28,(-1,0,0,0,1,0,0)),((1/1:ℚ),47,(0,0,0,0,0,0,0)),((1/1:ℚ),56,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 728=sourceKind 728 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (728 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row255] <;> ring

theorem row256_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 729) w=row256 w := by
  have hd : rowDerivative (sourceIndex 729)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 729)=0 := rfl
  have hs : sourceRows 729=[((1/1:ℚ),15,(0,0,0,0,0,0,0)),((-1/1:ℚ),30,(-1,0,0,0,1,0,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 729=sourceKind 729 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (729 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row256] <;> ring

theorem row257_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 730) w=row257 w := by
  have hd : rowDerivative (sourceIndex 730)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 730)=0 := rfl
  have hs : sourceRows 730=[((1/1:ℚ),16,(0,0,0,0,0,0,0)),((-1/1:ℚ),32,(-1,0,0,0,1,0,0)),((1/1:ℚ),49,(0,0,0,0,0,0,0)),((1/1:ℚ),64,(-2,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 730=sourceKind 730 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (730 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row257] <;> ring

theorem row258_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 731) w=row258 w := by
  have hd : rowDerivative (sourceIndex 731)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 731)=0 := rfl
  have hs : sourceRows 731=[((1/1:ℚ),2,(-2,0,0,0,0,0,0)),((1/1:ℚ),17,(0,0,0,0,0,0,0)),((-1/1:ℚ),34,(-1,0,0,0,1,0,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 731=sourceKind 731 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (731 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row258] <;> ring

theorem row259_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 732) w=row259 w := by
  have hd : rowDerivative (sourceIndex 732)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 732)=0 := rfl
  have hs : sourceRows 732=[((1/1:ℚ),6,(-2,0,0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,0,0,0)),((-1/1:ℚ),36,(-1,0,0,0,1,0,0)),((1/1:ℚ),51,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 732=sourceKind 732 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (732 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row259] <;> ring

theorem row260_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 733) w=row260 w := by
  have hd : rowDerivative (sourceIndex 733)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 733)=0 := rfl
  have hs : sourceRows 733=[((1/1:ℚ),10,(-2,0,0,0,0,0,0)),((1/1:ℚ),19,(0,0,0,0,0,0,0)),((-1/1:ℚ),38,(-1,0,0,0,1,0,0)),((1/1:ℚ),52,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 733=sourceKind 733 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (733 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row260] <;> ring

theorem row261_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 734) w=row261 w := by
  have hd : rowDerivative (sourceIndex 734)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 734)=0 := rfl
  have hs : sourceRows 734=[((1/1:ℚ),14,(-2,0,0,0,0,0,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((-1/1:ℚ),40,(-1,0,0,0,1,0,0)),((1/1:ℚ),53,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 734=sourceKind 734 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (734 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row261] <;> ring

theorem row262_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 738) w=row262 w := by
  have hd : rowDerivative (sourceIndex 738)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 738)=0 := rfl
  have hs : sourceRows 738=[((1/1:ℚ),24,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(-2,0,0,0,0,0,0)),((-1/1:ℚ),48,(-1,0,0,0,1,0,0)),((1/1:ℚ),57,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 738=sourceKind 738 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (738 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_filter,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row262] <;> ring

end QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftLinks
