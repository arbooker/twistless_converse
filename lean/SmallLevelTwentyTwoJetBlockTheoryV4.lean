module

public import SmallLevelTwentyOneThirdShiftScaleV1
public import SmallLevelTwentyTwoLaurentTheoryV4
public import SmallLevelTwentyTwoThirdJetDataBundleV4
public import SmallLevelTwentyTwoThirdJetKernel0V1
public import SmallLevelTwentyTwoThirdJetTriangularKernelBundleV4

/-! Consolidated chapter: SmallLevelTwentyTwoJetBlock. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyTwoJetBlockRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoJetBlock
open Complex SmallLevelFiniteShift SmallLevelTwentyTwoLaurent

def jetSlice (w : Fin 264→ℂ) (n : Fin 4) (j : Fin 66) : ℂ := w (finProdFinEquiv (n,j))

def jetBlockRow (η v : ℂ) (n : Fin 4) (i : Fin 68) (w : Fin 264→ℂ) : ℂ :=
  leadingRows η (-1) v (2/2^n.val) (3/3^n.val) (11/11^n.val) (-7/3) (jetSlice w n) i-
    ∑ a∈Finset.range n.val, (1/((a+1).factorial:ℂ))*
      positiveTaylorRows η (-1) v (2/2^n.val) (3/3^n.val) (11/11^n.val) a
        (jetSlice w (lowerIndex n a)) i

end SmallLevelTwentyTwoJetBlock
end
end

/-! ## SmallLevelTwentyTwoJetBlockLinksCaseIndexBundleSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoJetBlock
open Complex SmallLevelFiniteShift SmallLevelTwentyTwoLaurent SmallLevelTwentyTwoThirdJet

theorem link0_0 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 0 w=rows0 w 0 := by
  change jetBlockRow (-1) (-1) 0 0 w=(1)*w 0 + (22)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_0

theorem link0_1 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 1 w=rows0 w 1 := by
  change jetBlockRow (-1) (-1) 0 1 w=(1/198)*w 0 + (1)*w 1
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_1

theorem link0_2 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 2 w=rows0 w 2 := by
  change jetBlockRow (-1) (-1) 0 2 w=(1/22)*w 0 + (1)*w 3
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_2

theorem link0_3 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 3 w=rows0 w 3 := by
  change jetBlockRow (-1) (-1) 0 3 w=(1/198)*w 0 + (1)*w 65
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_3

theorem link0_4 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 4 w=rows0 w 4 := by
  change jetBlockRow (-1) (-1) 0 4 w=(1)*w 30 + ((-18))*w 65
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_4

theorem link0_5 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 5 w=rows0 w 5 := by
  change jetBlockRow (-1) (-1) 0 5 w=((-1)/2)*w 0 + (1)*w 33
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_5

theorem link0_6 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 6 w=rows0 w 6 := by
  change jetBlockRow (-1) (-1) 0 6 w=(1)*w 33 + (99/2)*w 64
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_6

theorem link0_7 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 7 w=rows0 w 7 := by
  change jetBlockRow (-1) (-1) 0 7 w=(1)*w 2 + (2/99)*w 33
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_7

theorem link0_8 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 8 w=rows0 w 8 := by
  change jetBlockRow (-1) (-1) 0 8 w=(1)*w 6 + (2/11)*w 33
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_8

theorem link0_9 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 9 w=rows0 w 9 := by
  change jetBlockRow (-1) (-1) 0 9 w=(1)*w 33 + (11/2)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_9

theorem link0_10 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 10 w=rows0 w 10 := by
  change jetBlockRow (-1) (-1) 0 10 w=(1)*w 34 + ((-2)/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_10

theorem link0_11 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 11 w=rows0 w 11 := by
  change jetBlockRow (-1) (-1) 0 11 w=(1)*w 32 + ((-2))*w 65
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_11

theorem link0_12 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 12 w=rows0 w 12 := by
  change jetBlockRow (-1) (-1) 0 12 w=(1)*w 36 + ((-2))*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_12

theorem link0_13 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 13 w=rows0 w 13 := by
  change jetBlockRow (-1) (-1) 0 13 w=(1)*w 9 + (9/22)*w 44
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_13

theorem link0_14 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 14 w=rows0 w 14 := by
  change jetBlockRow (-1) (-1) 0 14 w=(1)*w 11 + (11/18)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_14

theorem link0_15 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 15 w=rows0 w 15 := by
  change jetBlockRow (-1) (-1) 0 15 w=(1)*w 18 + (18/11)*w 55
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_15

theorem link0_16 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 16 w=rows0 w 16 := by
  change jetBlockRow (-1) (-1) 0 16 w=(1)*w 22 + (22/9)*w 57
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_16

theorem link0_17 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 17 w=rows0 w 17 := by
  change jetBlockRow (-1) (-1) 0 17 w=((-9))*w 4 + (1)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_17

theorem link0_18 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 18 w=rows0 w 18 := by
  change jetBlockRow (-1) (-1) 0 18 w=((-1)/9)*w 12 + (1)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_18

theorem link0_19 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 19 w=rows0 w 19 := by
  change jetBlockRow (-1) (-1) 0 19 w=(1)*w 35 + ((-1)/2)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_19

theorem link0_20 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 20 w=rows0 w 20 := by
  change jetBlockRow (-1) (-1) 0 20 w=(1)*w 18 + ((-18))*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_20

theorem link0_21 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 21 w=rows0 w 21 := by
  change jetBlockRow (-1) (-1) 0 21 w=(1)*w 27 + ((-9)/2)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_21

theorem link0_22 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 22 w=rows0 w 22 := by
  change jetBlockRow (-1) (-1) 0 22 w=(1)*w 37 + ((-1)/18)*w 42
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_22

theorem link0_23 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 23 w=rows0 w 23 := by
  change jetBlockRow (-1) (-1) 0 23 w=(1)*w 38 + ((-2)/9)*w 51
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_23

theorem link0_24 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 24 w=rows0 w 24 := by
  change jetBlockRow (-1) (-1) 0 24 w=(1)*w 39 + ((-1)/2)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_24

theorem link0_25 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 25 w=rows0 w 25 := by
  change jetBlockRow (-1) (-1) 0 25 w=(1)*w 42 + ((-2))*w 57
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_25

theorem link0_26 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 26 w=rows0 w 26 := by
  change jetBlockRow (-1) (-1) 0 26 w=(1)*w 45 + ((-9)/2)*w 58
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_26

theorem link0_27 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 27 w=rows0 w 27 := by
  change jetBlockRow (-1) (-1) 0 27 w=(1)*w 54 + ((-18))*w 59
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_27

theorem link0_28 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 28 w=rows0 w 28 := by
  change jetBlockRow (-1) (-1) 0 28 w=((-18))*w 7 + (1)*w 12
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_28

theorem link0_29 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 29 w=rows0 w 29 := by
  change jetBlockRow (-1) (-1) 0 29 w=((-9)/2)*w 8 + (1)*w 21
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_29

theorem link0_30 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 30 w=rows0 w 30 := by
  change jetBlockRow (-1) (-1) 0 30 w=((-2))*w 9 + (1)*w 24
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_30

theorem link0_31 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 31 w=rows0 w 31 := by
  change jetBlockRow (-1) (-1) 0 31 w=((-2)/9)*w 15 + (1)*w 28
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_31

theorem link0_32 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 32 w=rows0 w 32 := by
  change jetBlockRow (-1) (-1) 0 32 w=((-1)/18)*w 24 + (1)*w 29
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_32

theorem link0_33 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 33 w=rows0 w 33 := by
  change jetBlockRow (-1) (-1) 0 33 w=(1)*w 31 + ((-1)/18)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_33

theorem link0_34 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 34 w=rows0 w 34 := by
  change jetBlockRow (-1) (-1) 0 34 w=((-18))*w 5 + (1)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_34

theorem link0_35 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 35 w=rows0 w 35 := by
  change jetBlockRow (-1) (-1) 0 35 w=(2/11)*w 11 + (1)*w 24 + (2/11)*w 33 + (1)*w 46
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_35

theorem link0_36 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 36 w=rows0 w 36 := by
  change jetBlockRow (-1) (-1) 0 36 w=(1)*w 20 + (2/11)*w 33 + (1)*w 42 + (2/11)*w 55
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_36

theorem link0_37 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 37 w=rows0 w 37 := by
  change jetBlockRow (-1) (-1) 0 37 w=(1/2)*w 0 + (1/2)*w 6 + (1)*w 9 + (1/2)*w 12 + (1)*w 15 + (1/2)*w 18 + (1)*w 21 + (1/2)*w 24 + (1)*w 27 + (1/2)*w 30 + (1)*w 33 + (1/2)*w 36 + (1)*w 39 + (1/2)*w 42 + (1)*w 45 + (1/2)*w 48 + (1)*w 51 + (1/2)*w 54 + (1)*w 57 + (1)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_37

theorem link0_38 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 38 w=rows0 w 38 := by
  change jetBlockRow (-1) (-1) 0 38 w=(1/11)*w 0 + (1)*w 10 + (1/11)*w 22 + (1)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_38

theorem link0_39 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 39 w=rows0 w 39 := by
  change jetBlockRow (-1) (-1) 0 39 w=(1/11)*w 0 + (1)*w 12 + (1/11)*w 44 + (1)*w 56
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_39

theorem link0_40 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 40 w=rows0 w 40 := by
  change jetBlockRow (-1) (-1) 0 40 w=(1/22)*w 0 + (1/22)*w 22 + (1)*w 23 + (1)*w 45
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_40

theorem link0_41 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 41 w=rows0 w 41 := by
  change jetBlockRow (-1) (-1) 0 41 w=(1/22)*w 0 + (1)*w 21 + (1)*w 43 + (1/22)*w 44
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_41

theorem link0_42 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 42 w=rows0 w 42 := by
  change jetBlockRow (-1) (-1) 0 42 w=(1/18)*w 0 + (1/18)*w 6 + (1)*w 7 + (1/18)*w 12 + (1)*w 13 + (1/18)*w 18 + (1)*w 19 + (1/18)*w 24 + (1)*w 25 + (1/18)*w 30 + (1)*w 31 + (1/18)*w 36 + (1)*w 37 + (1/18)*w 42 + (1)*w 43 + (1)*w 49 + (1/18)*w 54 + (1)*w 55 + (1/18)*w 60 + (1)*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_42

theorem link0_43 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 43 w=rows0 w 43 := by
  change jetBlockRow (-1) (-1) 0 43 w=(2/9)*w 3 + (1)*w 4 + (1)*w 10 + (2/9)*w 15 + (1)*w 16 + (2/9)*w 21 + (1)*w 22 + (2/9)*w 27 + (1)*w 28 + (2/9)*w 33 + (1)*w 34 + (2/9)*w 39 + (1)*w 40 + (2/9)*w 45 + (1)*w 46 + (2/9)*w 51 + (1)*w 52 + (2/9)*w 57 + (1)*w 58 + (2/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_43

theorem link0_44 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 44 w=rows0 w 44 := by
  change jetBlockRow (-1) (-1) 0 44 w=(2/9)*w 3 + (1)*w 8 + (2/9)*w 9 + (1)*w 14 + (2/9)*w 15 + (1)*w 20 + (2/9)*w 21 + (1)*w 26 + (2/9)*w 27 + (1)*w 32 + (2/9)*w 33 + (1)*w 38 + (2/9)*w 39 + (1)*w 44 + (2/9)*w 45 + (1)*w 50 + (2/9)*w 51 + (1)*w 56 + (1)*w 62 + (2/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_44

theorem link0_45 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 45 w=rows0 w 45 := by
  change jetBlockRow (-1) (-1) 0 45 w=(1/18)*w 0 + (1)*w 5 + (1/18)*w 6 + (1)*w 11 + (1/18)*w 12 + (1)*w 17 + (1)*w 23 + (1/18)*w 24 + (1)*w 29 + (1/18)*w 30 + (1)*w 35 + (1/18)*w 36 + (1)*w 41 + (1/18)*w 42 + (1)*w 47 + (1/18)*w 48 + (1)*w 53 + (1/18)*w 54 + (1)*w 59 + (1/18)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_45

theorem link0_46 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 46 w=rows0 w 46 := by
  change jetBlockRow (-1) (-1) 0 46 w=(1)*w 0
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_46

theorem link0_47 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 47 w=rows0 w 47 := by
  change jetBlockRow (-1) (-1) 0 47 w=(1)*w 22 + (1)*w 44
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_47

theorem link0_48 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 48 w=rows0 w 48 := by
  change jetBlockRow (-1) (-1) 0 48 w=(1)*w 11 + (1)*w 55
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_48

theorem link0_49 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 49 w=rows0 w 49 := by
  change jetBlockRow (-1) (-1) 0 49 w=(1)*w 6 + (1)*w 12 + (1)*w 18 + (1)*w 24 + (1)*w 30 + (1)*w 36 + (1)*w 42 + (1)*w 48 + (1)*w 54 + (1)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_49

theorem link0_50 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 50 w=rows0 w 50 := by
  change jetBlockRow (-1) (-1) 0 50 w=(1)*w 9 + (1/2)*w 18 + (1)*w 42
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_50

theorem link0_51 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 51 w=rows0 w 51 := by
  change jetBlockRow (-1) (-1) 0 51 w=(1)*w 15 + (1/2)*w 30 + (1)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_51

theorem link0_52 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 52 w=rows0 w 52 := by
  change jetBlockRow (-1) (-1) 0 52 w=(1)*w 16 + (1/2)*w 32 + (1)*w 49
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_52

theorem link0_53 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 53 w=rows0 w 53 := by
  change jetBlockRow (-1) (-1) 0 53 w=(1)*w 17 + (1/2)*w 34 + (1)*w 50
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_53

theorem link0_54 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 54 w=rows0 w 54 := by
  change jetBlockRow (-1) (-1) 0 54 w=(1)*w 18 + (1/2)*w 36 + (1)*w 51
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_54

theorem link0_55 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 55 w=rows0 w 55 := by
  change jetBlockRow (-1) (-1) 0 55 w=(1)*w 5 + (1/2)*w 10 + (1)*w 38
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_55

theorem link0_56 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 56 w=rows0 w 56 := by
  change jetBlockRow (-1) (-1) 0 56 w=(1)*w 4 + (1/2)*w 8 + (1)*w 37
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_56

theorem link0_57 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 57 w=rows0 w 57 := by
  change jetBlockRow (-1) (-1) 0 57 w=(1)*w 7 + (7/9)*w 21 + (1)*w 29 + (1)*w 51 + (1/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_57

theorem link0_58 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 58 w=rows0 w 58 := by
  change jetBlockRow (-1) (-1) 0 58 w=(1)*w 4 + (7/9)*w 12 + (1)*w 26 + (1/9)*w 36 + (1)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_58

theorem link0_59 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 59 w=rows0 w 59 := by
  change jetBlockRow (-1) (-1) 0 59 w=(1)*w 13 + (1/2)*w 26 + (1)*w 46
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_59

theorem link0_60 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 60 w=rows0 w 60 := by
  change jetBlockRow (-1) (-1) 0 60 w=(1)*w 26 + (1/2)*w 52 + (1)*w 59
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_60

theorem link0_61 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 61 w=rows0 w 61 := by
  change jetBlockRow (-1) (-1) 0 61 w=(1)*w 19 + (1/2)*w 38 + (1)*w 52
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_61

theorem link0_62 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 62 w=rows0 w 62 := by
  change jetBlockRow (-1) (-1) 0 62 w=(1)*w 5 + (7/9)*w 15 + (1)*w 27 + (1/9)*w 45 + (1)*w 49
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_62

theorem link0_63 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 63 w=rows0 w 63 := by
  change jetBlockRow (-1) (-1) 0 63 w=(1)*w 7 + (1/2)*w 14 + (1)*w 40
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_63

theorem link0_64 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 64 w=rows0 w 64 := by
  change jetBlockRow (-1) (-1) 0 64 w=(1)*w 8 + (1/2)*w 16 + (1)*w 41
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_64

theorem link0_65 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 65 w=rows0 w 65 := by
  change jetBlockRow (-1) (-1) 0 65 w=(1)*w 14 + (1/2)*w 28 + (1)*w 47
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_65

theorem link0_66 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 66 w=rows0 w 66 := by
  change jetBlockRow (-1) (-1) 0 66 w=(1)*w 6 + (1/2)*w 12 + (1)*w 39
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_66

theorem link0_67 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 0 67 w=rows0 w 67 := by
  change jetBlockRow (-1) (-1) 0 67 w=(1)*w 28 + (1/2)*w 56 + (1)*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_67

theorem link0_68 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 0 w=rows0 w 68 := by
  change jetBlockRow (-1) (-1) 1 0 w=(22)*w 63 + (1)*w 66 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_68

theorem link0_69 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 1 w=rows0 w 69 := by
  change jetBlockRow (-1) (-1) 1 1 w=(1/3)*w 0 + (1)*w 66 + (1)*w 67
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_69

theorem link0_70 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 2 w=rows0 w 70 := by
  change jetBlockRow (-1) (-1) 1 2 w=(1)*w 0 + (1)*w 66 + (1)*w 69
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_70

theorem link0_71 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 3 w=rows0 w 71 := by
  change jetBlockRow (-1) (-1) 1 3 w=((-1)/3)*w 0 + (1)*w 66 + (1)*w 131
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_71

theorem link0_72 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 4 w=rows0 w 72 := by
  change jetBlockRow (-1) (-1) 1 4 w=(330)*w 65 + (1)*w 96 + ((-1))*w 131
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_72

theorem link0_73 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 5 w=rows0 w 73 := by
  change jetBlockRow (-1) (-1) 1 5 w=(55)*w 0 + ((-1))*w 66 + (1)*w 99
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_73

theorem link0_74 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 6 w=rows0 w 74 := by
  change jetBlockRow (-1) (-1) 1 6 w=(33)*w 64 + (1)*w 99 + (1)*w 130
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_74

theorem link0_75 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 7 w=rows0 w 75 := by
  change jetBlockRow (-1) (-1) 1 7 w=(2/3)*w 33 + (1)*w 68 + (1)*w 99
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_75

theorem link0_76 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 8 w=rows0 w 76 := by
  change jetBlockRow (-1) (-1) 1 8 w=(2)*w 33 + (1)*w 72 + (1)*w 99
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_76

theorem link0_77 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 9 w=rows0 w 77 := by
  change jetBlockRow (-1) (-1) 1 9 w=(11)*w 60 + (1)*w 99 + (1)*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_77

theorem link0_78 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 10 w=rows0 w 78 := by
  change jetBlockRow (-1) (-1) 1 10 w=((-110)/3)*w 63 + (1)*w 100 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_78

theorem link0_79 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 11 w=rows0 w 79 := by
  change jetBlockRow (-1) (-1) 1 11 w=(66)*w 65 + (1)*w 98 + ((-1))*w 131
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_79

theorem link0_80 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 12 w=rows0 w 80 := by
  change jetBlockRow (-1) (-1) 1 12 w=((-66))*w 63 + (1)*w 102 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_80

theorem link0_81 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 13 w=rows0 w 81 := by
  change jetBlockRow (-1) (-1) 1 13 w=(3)*w 44 + (1)*w 75 + (1)*w 110
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_81

theorem link0_82 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 14 w=rows0 w 82 := by
  change jetBlockRow (-1) (-1) 1 14 w=(11/3)*w 48 + (1)*w 77 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_82

theorem link0_83 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 15 w=rows0 w 83 := by
  change jetBlockRow (-1) (-1) 1 15 w=(6)*w 55 + (1)*w 84 + (1)*w 121
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_83

theorem link0_84 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 16 w=rows0 w 84 := by
  change jetBlockRow (-1) (-1) 1 16 w=(22/3)*w 57 + (1)*w 88 + (1)*w 123
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_84

theorem link0_85 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 17 w=rows0 w 85 := by
  change jetBlockRow (-1) (-1) 1 17 w=(66)*w 4 + ((-1))*w 70 + (1)*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_85

theorem link0_86 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 18 w=rows0 w 86 := by
  change jetBlockRow (-1) (-1) 1 18 w=(22/3)*w 12 + ((-1))*w 78 + (1)*w 128
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_86

theorem link0_87 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 19 w=rows0 w 87 := by
  change jetBlockRow (-1) (-1) 1 19 w=((-33))*w 62 + (1)*w 101 + ((-1))*w 128
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_87

theorem link0_88 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 20 w=rows0 w 88 := by
  change jetBlockRow (-1) (-1) 1 20 w=(66)*w 61 + (1)*w 84 + ((-1))*w 127
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_88

theorem link0_89 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 21 w=rows0 w 89 := by
  change jetBlockRow (-1) (-1) 1 21 w=(33)*w 62 + (1)*w 93 + ((-1))*w 128
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_89

theorem link0_90 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 22 w=rows0 w 90 := by
  change jetBlockRow (-1) (-1) 1 22 w=((-11)/3)*w 42 + (1)*w 103 + ((-1))*w 108
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_90

theorem link0_91 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 23 w=rows0 w 91 := by
  change jetBlockRow (-1) (-1) 1 23 w=((-22)/3)*w 51 + (1)*w 104 + ((-1))*w 117
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_91

theorem link0_92 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 24 w=rows0 w 92 := by
  change jetBlockRow (-1) (-1) 1 24 w=((-11))*w 54 + (1)*w 105 + ((-1))*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_92

theorem link0_93 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 25 w=rows0 w 93 := by
  change jetBlockRow (-1) (-1) 1 25 w=((-22))*w 57 + (1)*w 108 + ((-1))*w 123
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_93

theorem link0_94 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 26 w=rows0 w 94 := by
  change jetBlockRow (-1) (-1) 1 26 w=((-33))*w 58 + (1)*w 111 + ((-1))*w 124
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_94

theorem link0_95 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 27 w=rows0 w 95 := by
  change jetBlockRow (-1) (-1) 1 27 w=((-66))*w 59 + (1)*w 120 + ((-1))*w 125
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_95

theorem link0_96 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 28 w=rows0 w 96 := by
  change jetBlockRow (-1) (-1) 1 28 w=(66)*w 7 + ((-1))*w 73 + (1)*w 78
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_96

theorem link0_97 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 29 w=rows0 w 97 := by
  change jetBlockRow (-1) (-1) 1 29 w=(33)*w 8 + ((-1))*w 74 + (1)*w 87
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_97

theorem link0_98 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 30 w=rows0 w 98 := by
  change jetBlockRow (-1) (-1) 1 30 w=(22)*w 9 + ((-1))*w 75 + (1)*w 90
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_98

theorem link0_99 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 31 w=rows0 w 99 := by
  change jetBlockRow (-1) (-1) 1 31 w=(22/3)*w 15 + ((-1))*w 81 + (1)*w 94
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_99

theorem link0_100 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 32 w=rows0 w 100 := by
  change jetBlockRow (-1) (-1) 1 32 w=(11/3)*w 24 + ((-1))*w 90 + (1)*w 95
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_100

theorem link0_101 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 33 w=rows0 w 101 := by
  change jetBlockRow (-1) (-1) 1 33 w=((-11)/3)*w 54 + (1)*w 97 + ((-1))*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_101

theorem link0_102 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 34 w=rows0 w 102 := by
  change jetBlockRow (-1) (-1) 1 34 w=((-66))*w 5 + ((-1))*w 71 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_102

theorem link0_103 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 35 w=rows0 w 103 := by
  change jetBlockRow (-1) (-1) 1 35 w=(6)*w 11 + (6)*w 33 + (1)*w 77 + (1)*w 90 + (1)*w 99 + (1)*w 112
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_103

theorem link0_104 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 36 w=rows0 w 104 := by
  change jetBlockRow (-1) (-1) 1 36 w=((-6))*w 33 + ((-6))*w 55 + (1)*w 86 + (1)*w 99 + (1)*w 108 + (1)*w 121
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_104

theorem link0_105 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 37 w=rows0 w 105 := by
  change jetBlockRow (-1) (-1) 1 37 w=(11)*w 0 + (11)*w 6 + (11)*w 12 + (11)*w 18 + (11)*w 24 + (11)*w 30 + (11)*w 36 + (11)*w 42 + (11)*w 48 + (11)*w 54 + (1)*w 66 + (1)*w 72 + (1)*w 75 + (1)*w 78 + (1)*w 81 + (1)*w 84 + (1)*w 87 + (1)*w 90 + (1)*w 93 + (1)*w 96 + (1)*w 99 + (1)*w 102 + (1)*w 105 + (1)*w 108 + (1)*w 111 + (1)*w 114 + (1)*w 117 + (1)*w 120 + (1)*w 123 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_105

theorem link0_106 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 38 w=rows0 w 106 := by
  change jetBlockRow (-1) (-1) 1 38 w=((-6))*w 0 + ((-6))*w 22 + (1)*w 66 + (1)*w 76 + (1)*w 88 + (1)*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_106

theorem link0_107 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 39 w=rows0 w 107 := by
  change jetBlockRow (-1) (-1) 1 39 w=(6)*w 0 + (6)*w 44 + (1)*w 66 + (1)*w 78 + (1)*w 110 + (1)*w 122
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_107

theorem link0_108 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 40 w=rows0 w 108 := by
  change jetBlockRow (-1) (-1) 1 40 w=(3)*w 0 + (3)*w 22 + (1)*w 66 + (1)*w 88 + (1)*w 89 + (1)*w 111
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_108

theorem link0_109 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 41 w=rows0 w 109 := by
  change jetBlockRow (-1) (-1) 1 41 w=((-3))*w 0 + ((-3))*w 44 + (1)*w 66 + (1)*w 87 + (1)*w 109 + (1)*w 110
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_109

theorem link0_110 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 42 w=rows0 w 110 := by
  change jetBlockRow (-1) (-1) 1 42 w=(11/3)*w 0 + (11/3)*w 6 + (11/3)*w 12 + (11/3)*w 18 + (11/3)*w 24 + (11/3)*w 30 + (11/3)*w 36 + (11/3)*w 42 + (11/3)*w 54 + (11/3)*w 60 + (1)*w 66 + (1)*w 72 + (1)*w 73 + (1)*w 78 + (1)*w 79 + (1)*w 84 + (1)*w 85 + (1)*w 90 + (1)*w 91 + (1)*w 96 + (1)*w 97 + (1)*w 102 + (1)*w 103 + (1)*w 108 + (1)*w 109 + (1)*w 115 + (1)*w 120 + (1)*w 121 + (1)*w 126 + (1)*w 127
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_110

theorem link0_111 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 43 w=rows0 w 111 := by
  change jetBlockRow (-1) (-1) 1 43 w=((-22)/3)*w 3 + ((-22)/3)*w 15 + ((-22)/3)*w 21 + ((-22)/3)*w 27 + ((-22)/3)*w 33 + ((-22)/3)*w 39 + ((-22)/3)*w 45 + ((-22)/3)*w 51 + ((-22)/3)*w 57 + ((-22)/3)*w 63 + (1)*w 69 + (1)*w 70 + (1)*w 76 + (1)*w 81 + (1)*w 82 + (1)*w 87 + (1)*w 88 + (1)*w 93 + (1)*w 94 + (1)*w 99 + (1)*w 100 + (1)*w 105 + (1)*w 106 + (1)*w 111 + (1)*w 112 + (1)*w 117 + (1)*w 118 + (1)*w 123 + (1)*w 124 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_111

theorem link0_112 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 44 w=rows0 w 112 := by
  change jetBlockRow (-1) (-1) 1 44 w=(22/3)*w 3 + (22/3)*w 9 + (22/3)*w 15 + (22/3)*w 21 + (22/3)*w 27 + (22/3)*w 33 + (22/3)*w 39 + (22/3)*w 45 + (22/3)*w 51 + (22/3)*w 63 + (1)*w 69 + (1)*w 74 + (1)*w 75 + (1)*w 80 + (1)*w 81 + (1)*w 86 + (1)*w 87 + (1)*w 92 + (1)*w 93 + (1)*w 98 + (1)*w 99 + (1)*w 104 + (1)*w 105 + (1)*w 110 + (1)*w 111 + (1)*w 116 + (1)*w 117 + (1)*w 122 + (1)*w 128 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_112

theorem link0_113 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 45 w=rows0 w 113 := by
  change jetBlockRow (-1) (-1) 1 45 w=((-11)/3)*w 0 + ((-11)/3)*w 6 + ((-11)/3)*w 12 + ((-11)/3)*w 24 + ((-11)/3)*w 30 + ((-11)/3)*w 36 + ((-11)/3)*w 42 + ((-11)/3)*w 48 + ((-11)/3)*w 54 + ((-11)/3)*w 60 + (1)*w 66 + (1)*w 71 + (1)*w 72 + (1)*w 77 + (1)*w 78 + (1)*w 83 + (1)*w 89 + (1)*w 90 + (1)*w 95 + (1)*w 96 + (1)*w 101 + (1)*w 102 + (1)*w 107 + (1)*w 108 + (1)*w 113 + (1)*w 114 + (1)*w 119 + (1)*w 120 + (1)*w 125 + (1)*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_113

theorem link0_114 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 46 w=rows0 w 114 := by
  change jetBlockRow (-1) (-1) 1 46 w=(1)*w 66
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_114

theorem link0_115 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 47 w=rows0 w 115 := by
  change jetBlockRow (-1) (-1) 1 47 w=(1)*w 88 + (1)*w 110
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_115

theorem link0_116 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 48 w=rows0 w 116 := by
  change jetBlockRow (-1) (-1) 1 48 w=(1)*w 77 + (1)*w 121
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_116

theorem link0_117 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 49 w=rows0 w 117 := by
  change jetBlockRow (-1) (-1) 1 49 w=(1)*w 72 + (1)*w 78 + (1)*w 84 + (1)*w 90 + (1)*w 96 + (1)*w 102 + (1)*w 108 + (1)*w 114 + (1)*w 120 + (1)*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_117

theorem link0_118 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 50 w=rows0 w 118 := by
  change jetBlockRow (-1) (-1) 1 50 w=(1)*w 75 + (1)*w 84 + (1)*w 108
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_118

theorem link0_119 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 51 w=rows0 w 119 := by
  change jetBlockRow (-1) (-1) 1 51 w=(1)*w 81 + (1)*w 96 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_119

theorem link0_120 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 52 w=rows0 w 120 := by
  change jetBlockRow (-1) (-1) 1 52 w=(1)*w 82 + (1)*w 98 + (1)*w 115
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_120

theorem link0_121 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 53 w=rows0 w 121 := by
  change jetBlockRow (-1) (-1) 1 53 w=(1)*w 83 + (1)*w 100 + (1)*w 116
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_121

theorem link0_122 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 54 w=rows0 w 122 := by
  change jetBlockRow (-1) (-1) 1 54 w=(1)*w 84 + (1)*w 102 + (1)*w 117
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_122

theorem link0_123 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 55 w=rows0 w 123 := by
  change jetBlockRow (-1) (-1) 1 55 w=(1)*w 71 + (1)*w 76 + (1)*w 104
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_123

theorem link0_124 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 56 w=rows0 w 124 := by
  change jetBlockRow (-1) (-1) 1 56 w=(1)*w 70 + (1)*w 74 + (1)*w 103
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_124

theorem link0_125 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 57 w=rows0 w 125 := by
  change jetBlockRow (-1) (-1) 1 57 w=(1)*w 73 + (7/3)*w 87 + (1)*w 95 + (1)*w 117 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_125

theorem link0_126 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 58 w=rows0 w 126 := by
  change jetBlockRow (-1) (-1) 1 58 w=(1)*w 70 + (7/3)*w 78 + (1)*w 92 + (1)*w 102 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_126

theorem link0_127 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 59 w=rows0 w 127 := by
  change jetBlockRow (-1) (-1) 1 59 w=(1)*w 79 + (1)*w 92 + (1)*w 112
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_127

theorem link0_128 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 60 w=rows0 w 128 := by
  change jetBlockRow (-1) (-1) 1 60 w=(1)*w 92 + (1)*w 118 + (1)*w 125
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_128

theorem link0_129 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 61 w=rows0 w 129 := by
  change jetBlockRow (-1) (-1) 1 61 w=(1)*w 85 + (1)*w 104 + (1)*w 118
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_129

theorem link0_130 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 62 w=rows0 w 130 := by
  change jetBlockRow (-1) (-1) 1 62 w=(1)*w 71 + (7/3)*w 81 + (1)*w 93 + (1)*w 111 + (1)*w 115
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_130

theorem link0_131 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 63 w=rows0 w 131 := by
  change jetBlockRow (-1) (-1) 1 63 w=(1)*w 73 + (1)*w 80 + (1)*w 106
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_131

theorem link0_132 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 64 w=rows0 w 132 := by
  change jetBlockRow (-1) (-1) 1 64 w=(1)*w 74 + (1)*w 82 + (1)*w 107
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_132

theorem link0_133 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 65 w=rows0 w 133 := by
  change jetBlockRow (-1) (-1) 1 65 w=(1)*w 80 + (1)*w 94 + (1)*w 113
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_133

theorem link0_134 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 66 w=rows0 w 134 := by
  change jetBlockRow (-1) (-1) 1 66 w=(1)*w 72 + (1)*w 78 + (1)*w 105
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_134

theorem link0_135 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 1 67 w=rows0 w 135 := by
  change jetBlockRow (-1) (-1) 1 67 w=(1)*w 94 + (1)*w 122 + (1)*w 127
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_135

theorem link0_136 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 0 w=rows0 w 136 := by
  change jetBlockRow (-1) (-1) 2 0 w=(11)*w 63 + (1)*w 129 + (1)*w 132 + (1/22)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_136

theorem link0_137 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 1 w=rows0 w 137 := by
  change jetBlockRow (-1) (-1) 2 1 w=(11)*w 0 + (66)*w 66 + (198)*w 132 + (1)*w 133
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_137

theorem link0_138 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 2 w=rows0 w 138 := by
  change jetBlockRow (-1) (-1) 2 2 w=(11)*w 0 + (22)*w 66 + (22)*w 132 + (1)*w 135
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_138

theorem link0_139 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 3 w=rows0 w 139 := by
  change jetBlockRow (-1) (-1) 2 3 w=(11)*w 0 + ((-66))*w 66 + (198)*w 132 + (1)*w 197
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_139

theorem link0_140 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 4 w=rows0 w 140 := by
  change jetBlockRow (-1) (-1) 2 4 w=((-3025))*w 65 + (55/3)*w 131 + (1)*w 162 + ((-1)/18)*w 197
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_140

theorem link0_141 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 5 w=rows0 w 141 := by
  change jetBlockRow (-1) (-1) 2 5 w=((-3025))*w 0 + (110)*w 66 + ((-2))*w 132 + (1)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_141

theorem link0_142 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 6 w=rows0 w 142 := by
  change jetBlockRow (-1) (-1) 2 6 w=(11)*w 64 + (2/3)*w 130 + (1)*w 165 + (2/99)*w 196
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_142

theorem link0_143 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 7 w=rows0 w 143 := by
  change jetBlockRow (-1) (-1) 2 7 w=(11)*w 33 + (33)*w 99 + (1)*w 134 + (99/2)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_143

theorem link0_144 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 8 w=rows0 w 144 := by
  change jetBlockRow (-1) (-1) 2 8 w=(11)*w 33 + (11)*w 99 + (1)*w 138 + (11/2)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_144

theorem link0_145 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 9 w=rows0 w 145 := by
  change jetBlockRow (-1) (-1) 2 9 w=(11)*w 60 + (2)*w 126 + (1)*w 165 + (2/11)*w 192
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_145

theorem link0_146 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 10 w=rows0 w 146 := by
  change jetBlockRow (-1) (-1) 2 10 w=((-3025))*w 63 + ((-165))*w 129 + (1)*w 166 + ((-9)/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_146

theorem link0_147 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 11 w=rows0 w 147 := by
  change jetBlockRow (-1) (-1) 2 11 w=((-1089))*w 65 + (33)*w 131 + (1)*w 164 + ((-1)/2)*w 197
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_147

theorem link0_148 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 12 w=rows0 w 148 := by
  change jetBlockRow (-1) (-1) 2 12 w=((-1089))*w 63 + ((-33))*w 129 + (1)*w 168 + ((-1)/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_148

theorem link0_149 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 13 w=rows0 w 149 := by
  change jetBlockRow (-1) (-1) 2 13 w=(11)*w 44 + (22/3)*w 110 + (1)*w 141 + (22/9)*w 176
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_149

theorem link0_150 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 14 w=rows0 w 150 := by
  change jetBlockRow (-1) (-1) 2 14 w=(11)*w 48 + (6)*w 114 + (1)*w 143 + (18/11)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_150

theorem link0_151 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 15 w=rows0 w 151 := by
  change jetBlockRow (-1) (-1) 2 15 w=(11)*w 55 + (11/3)*w 121 + (1)*w 150 + (11/18)*w 187
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_151

theorem link0_152 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 16 w=rows0 w 152 := by
  change jetBlockRow (-1) (-1) 2 16 w=(11)*w 57 + (3)*w 123 + (1)*w 154 + (9/22)*w 189
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_152

theorem link0_153 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 17 w=rows0 w 153 := by
  change jetBlockRow (-1) (-1) 2 17 w=((-242))*w 4 + (22/3)*w 70 + ((-1)/9)*w 136 + (1)*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_153

theorem link0_154 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 18 w=rows0 w 154 := by
  change jetBlockRow (-1) (-1) 2 18 w=((-242))*w 12 + (66)*w 78 + ((-9))*w 144 + (1)*w 194
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_154

theorem link0_155 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 19 w=rows0 w 155 := by
  change jetBlockRow (-1) (-1) 2 19 w=((-1089))*w 62 + ((-66))*w 128 + (1)*w 167 + ((-2))*w 194
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_155

theorem link0_156 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 20 w=rows0 w 156 := by
  change jetBlockRow (-1) (-1) 2 20 w=((-121))*w 61 + (11/3)*w 127 + (1)*w 150 + ((-1)/18)*w 193
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_156

theorem link0_157 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 21 w=rows0 w 157 := by
  change jetBlockRow (-1) (-1) 2 21 w=((-121))*w 62 + (22/3)*w 128 + (1)*w 159 + ((-2)/9)*w 194
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_157

theorem link0_158 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 22 w=rows0 w 158 := by
  change jetBlockRow (-1) (-1) 2 22 w=((-121))*w 42 + ((-66))*w 108 + (1)*w 169 + ((-18))*w 174
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_158

theorem link0_159 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 23 w=rows0 w 159 := by
  change jetBlockRow (-1) (-1) 2 23 w=((-121))*w 51 + ((-33))*w 117 + (1)*w 170 + ((-9)/2)*w 183
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_159

theorem link0_160 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 24 w=rows0 w 160 := by
  change jetBlockRow (-1) (-1) 2 24 w=((-121))*w 54 + ((-22))*w 120 + (1)*w 171 + ((-2))*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_160

theorem link0_161 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 25 w=rows0 w 161 := by
  change jetBlockRow (-1) (-1) 2 25 w=((-121))*w 57 + ((-11))*w 123 + (1)*w 174 + ((-1)/2)*w 189
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_161

theorem link0_162 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 26 w=rows0 w 162 := by
  change jetBlockRow (-1) (-1) 2 26 w=((-121))*w 58 + ((-22)/3)*w 124 + (1)*w 177 + ((-2)/9)*w 190
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_162

theorem link0_163 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 27 w=rows0 w 163 := by
  change jetBlockRow (-1) (-1) 2 27 w=((-121))*w 59 + ((-11)/3)*w 125 + (1)*w 186 + ((-1)/18)*w 191
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_163

theorem link0_164 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 28 w=rows0 w 164 := by
  change jetBlockRow (-1) (-1) 2 28 w=((-121))*w 7 + (11/3)*w 73 + ((-1)/18)*w 139 + (1)*w 144
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_164

theorem link0_165 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 29 w=rows0 w 165 := by
  change jetBlockRow (-1) (-1) 2 29 w=((-121))*w 8 + (22/3)*w 74 + ((-2)/9)*w 140 + (1)*w 153
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_165

theorem link0_166 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 30 w=rows0 w 166 := by
  change jetBlockRow (-1) (-1) 2 30 w=((-121))*w 9 + (11)*w 75 + ((-1)/2)*w 141 + (1)*w 156
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_166

theorem link0_167 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 31 w=rows0 w 167 := by
  change jetBlockRow (-1) (-1) 2 31 w=((-121))*w 15 + (33)*w 81 + ((-9)/2)*w 147 + (1)*w 160
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_167

theorem link0_168 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 32 w=rows0 w 168 := by
  change jetBlockRow (-1) (-1) 2 32 w=((-121))*w 24 + (66)*w 90 + ((-18))*w 156 + (1)*w 161
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_168

theorem link0_169 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 33 w=rows0 w 169 := by
  change jetBlockRow (-1) (-1) 2 33 w=((-121))*w 54 + ((-66))*w 120 + (1)*w 163 + ((-18))*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_169

theorem link0_170 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 34 w=rows0 w 170 := by
  change jetBlockRow (-1) (-1) 2 34 w=((-121))*w 5 + ((-11)/3)*w 71 + ((-1)/18)*w 137 + (1)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_170

theorem link0_171 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 35 w=rows0 w 171 := by
  change jetBlockRow (-1) (-1) 2 35 w=(99)*w 11 + (99)*w 33 + (33)*w 77 + (33)*w 99 + (11/2)*w 143 + (1)*w 156 + (11/2)*w 165 + (1)*w 178
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_171

theorem link0_172 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 36 w=rows0 w 172 := by
  change jetBlockRow (-1) (-1) 2 36 w=(99)*w 33 + (99)*w 55 + ((-33))*w 99 + ((-33))*w 121 + (1)*w 152 + (11/2)*w 165 + (1)*w 174 + (11/2)*w 187
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_172

theorem link0_173 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 37 w=rows0 w 173 := by
  change jetBlockRow (-1) (-1) 2 37 w=(121)*w 0 + (121)*w 6 + (121)*w 12 + (121)*w 18 + (121)*w 24 + (121)*w 30 + (121)*w 36 + (121)*w 42 + (121)*w 48 + (121)*w 54 + (22)*w 66 + (22)*w 72 + (22)*w 78 + (22)*w 84 + (22)*w 90 + (22)*w 96 + (22)*w 102 + (22)*w 108 + (22)*w 114 + (22)*w 120 + (2)*w 132 + (2)*w 138 + (1)*w 141 + (2)*w 144 + (1)*w 147 + (2)*w 150 + (1)*w 153 + (2)*w 156 + (1)*w 159 + (2)*w 162 + (1)*w 165 + (2)*w 168 + (1)*w 171 + (2)*w 174 + (1)*w 177 + (2)*w 180 + (1)*w 183 + (2)*w 186 + (1)*w 189 + (1)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_173

theorem link0_174 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 38 w=rows0 w 174 := by
  change jetBlockRow (-1) (-1) 2 38 w=(198)*w 0 + (198)*w 22 + ((-66))*w 66 + ((-66))*w 88 + (11)*w 132 + (1)*w 142 + (11)*w 154 + (1)*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_174

theorem link0_175 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 39 w=rows0 w 175 := by
  change jetBlockRow (-1) (-1) 2 39 w=(198)*w 0 + (198)*w 44 + (66)*w 66 + (66)*w 110 + (11)*w 132 + (1)*w 144 + (11)*w 176 + (1)*w 188
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_175

theorem link0_176 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 40 w=rows0 w 176 := by
  change jetBlockRow (-1) (-1) 2 40 w=(99)*w 0 + (99)*w 22 + (66)*w 66 + (66)*w 88 + (22)*w 132 + (22)*w 154 + (1)*w 155 + (1)*w 177
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_176

theorem link0_177 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 41 w=rows0 w 177 := by
  change jetBlockRow (-1) (-1) 2 41 w=(99)*w 0 + (99)*w 44 + ((-66))*w 66 + ((-66))*w 110 + (22)*w 132 + (1)*w 153 + (1)*w 175 + (22)*w 176
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_177

theorem link0_178 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 42 w=rows0 w 178 := by
  change jetBlockRow (-1) (-1) 2 42 w=(121)*w 0 + (121)*w 6 + (121)*w 12 + (121)*w 18 + (121)*w 24 + (121)*w 30 + (121)*w 36 + (121)*w 42 + (121)*w 54 + (121)*w 60 + (66)*w 66 + (66)*w 72 + (66)*w 78 + (66)*w 84 + (66)*w 90 + (66)*w 96 + (66)*w 102 + (66)*w 108 + (66)*w 120 + (66)*w 126 + (18)*w 132 + (18)*w 138 + (1)*w 139 + (18)*w 144 + (1)*w 145 + (18)*w 150 + (1)*w 151 + (18)*w 156 + (1)*w 157 + (18)*w 162 + (1)*w 163 + (18)*w 168 + (1)*w 169 + (18)*w 174 + (1)*w 175 + (1)*w 181 + (18)*w 186 + (1)*w 187 + (18)*w 192 + (1)*w 193
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_178

theorem link0_179 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 43 w=rows0 w 179 := by
  change jetBlockRow (-1) (-1) 2 43 w=(121)*w 3 + (121)*w 15 + (121)*w 21 + (121)*w 27 + (121)*w 33 + (121)*w 39 + (121)*w 45 + (121)*w 51 + (121)*w 57 + (121)*w 63 + ((-33))*w 69 + ((-33))*w 81 + ((-33))*w 87 + ((-33))*w 93 + ((-33))*w 99 + ((-33))*w 105 + ((-33))*w 111 + ((-33))*w 117 + ((-33))*w 123 + ((-33))*w 129 + (9/2)*w 135 + (1)*w 136 + (1)*w 142 + (9/2)*w 147 + (1)*w 148 + (9/2)*w 153 + (1)*w 154 + (9/2)*w 159 + (1)*w 160 + (9/2)*w 165 + (1)*w 166 + (9/2)*w 171 + (1)*w 172 + (9/2)*w 177 + (1)*w 178 + (9/2)*w 183 + (1)*w 184 + (9/2)*w 189 + (1)*w 190 + (9/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_179

theorem link0_180 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 44 w=rows0 w 180 := by
  change jetBlockRow (-1) (-1) 2 44 w=(121)*w 3 + (121)*w 9 + (121)*w 15 + (121)*w 21 + (121)*w 27 + (121)*w 33 + (121)*w 39 + (121)*w 45 + (121)*w 51 + (121)*w 63 + (33)*w 69 + (33)*w 75 + (33)*w 81 + (33)*w 87 + (33)*w 93 + (33)*w 99 + (33)*w 105 + (33)*w 111 + (33)*w 117 + (33)*w 129 + (9/2)*w 135 + (1)*w 140 + (9/2)*w 141 + (1)*w 146 + (9/2)*w 147 + (1)*w 152 + (9/2)*w 153 + (1)*w 158 + (9/2)*w 159 + (1)*w 164 + (9/2)*w 165 + (1)*w 170 + (9/2)*w 171 + (1)*w 176 + (9/2)*w 177 + (1)*w 182 + (9/2)*w 183 + (1)*w 188 + (1)*w 194 + (9/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_180

theorem link0_181 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 45 w=rows0 w 181 := by
  change jetBlockRow (-1) (-1) 2 45 w=(121)*w 0 + (121)*w 6 + (121)*w 12 + (121)*w 24 + (121)*w 30 + (121)*w 36 + (121)*w 42 + (121)*w 48 + (121)*w 54 + (121)*w 60 + ((-66))*w 66 + ((-66))*w 72 + ((-66))*w 78 + ((-66))*w 90 + ((-66))*w 96 + ((-66))*w 102 + ((-66))*w 108 + ((-66))*w 114 + ((-66))*w 120 + ((-66))*w 126 + (18)*w 132 + (1)*w 137 + (18)*w 138 + (1)*w 143 + (18)*w 144 + (1)*w 149 + (1)*w 155 + (18)*w 156 + (1)*w 161 + (18)*w 162 + (1)*w 167 + (18)*w 168 + (1)*w 173 + (18)*w 174 + (1)*w 179 + (18)*w 180 + (1)*w 185 + (18)*w 186 + (1)*w 191 + (18)*w 192
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_181

theorem link0_182 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 46 w=rows0 w 182 := by
  change jetBlockRow (-1) (-1) 2 46 w=(1)*w 132
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_182

theorem link0_183 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 47 w=rows0 w 183 := by
  change jetBlockRow (-1) (-1) 2 47 w=(1)*w 154 + (1)*w 176
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_183

theorem link0_184 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 48 w=rows0 w 184 := by
  change jetBlockRow (-1) (-1) 2 48 w=(1)*w 143 + (1)*w 187
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_184

theorem link0_185 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 49 w=rows0 w 185 := by
  change jetBlockRow (-1) (-1) 2 49 w=(1)*w 138 + (1)*w 144 + (1)*w 150 + (1)*w 156 + (1)*w 162 + (1)*w 168 + (1)*w 174 + (1)*w 180 + (1)*w 186 + (1)*w 192
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_185

theorem link0_186 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 50 w=rows0 w 186 := by
  change jetBlockRow (-1) (-1) 2 50 w=(1)*w 141 + (2)*w 150 + (1)*w 174
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_186

theorem link0_187 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 51 w=rows0 w 187 := by
  change jetBlockRow (-1) (-1) 2 51 w=(1)*w 147 + (2)*w 162 + (1)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_187

theorem link0_188 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 52 w=rows0 w 188 := by
  change jetBlockRow (-1) (-1) 2 52 w=(1)*w 148 + (2)*w 164 + (1)*w 181
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_188

theorem link0_189 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 53 w=rows0 w 189 := by
  change jetBlockRow (-1) (-1) 2 53 w=(1)*w 149 + (2)*w 166 + (1)*w 182
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_189

theorem link0_190 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 54 w=rows0 w 190 := by
  change jetBlockRow (-1) (-1) 2 54 w=(1)*w 150 + (2)*w 168 + (1)*w 183
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_190

theorem link0_191 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 55 w=rows0 w 191 := by
  change jetBlockRow (-1) (-1) 2 55 w=(1)*w 137 + (2)*w 142 + (1)*w 170
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_191

theorem link0_192 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 56 w=rows0 w 192 := by
  change jetBlockRow (-1) (-1) 2 56 w=(1)*w 136 + (2)*w 140 + (1)*w 169
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_192

theorem link0_193 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 57 w=rows0 w 193 := by
  change jetBlockRow (-1) (-1) 2 57 w=(1)*w 139 + (7)*w 153 + (1)*w 161 + (1)*w 183 + (9)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_193

theorem link0_194 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 58 w=rows0 w 194 := by
  change jetBlockRow (-1) (-1) 2 58 w=(1)*w 136 + (7)*w 144 + (1)*w 158 + (9)*w 168 + (1)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_194

theorem link0_195 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 59 w=rows0 w 195 := by
  change jetBlockRow (-1) (-1) 2 59 w=(1)*w 145 + (2)*w 158 + (1)*w 178
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_195

theorem link0_196 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 60 w=rows0 w 196 := by
  change jetBlockRow (-1) (-1) 2 60 w=(1)*w 158 + (2)*w 184 + (1)*w 191
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_196

theorem link0_197 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 61 w=rows0 w 197 := by
  change jetBlockRow (-1) (-1) 2 61 w=(1)*w 151 + (2)*w 170 + (1)*w 184
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_197

theorem link0_198 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 62 w=rows0 w 198 := by
  change jetBlockRow (-1) (-1) 2 62 w=(1)*w 137 + (7)*w 147 + (1)*w 159 + (9)*w 177 + (1)*w 181
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_198

theorem link0_199 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 63 w=rows0 w 199 := by
  change jetBlockRow (-1) (-1) 2 63 w=(1)*w 139 + (2)*w 146 + (1)*w 172
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_199

theorem link0_200 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 64 w=rows0 w 200 := by
  change jetBlockRow (-1) (-1) 2 64 w=(1)*w 140 + (2)*w 148 + (1)*w 173
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_200

theorem link0_201 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 65 w=rows0 w 201 := by
  change jetBlockRow (-1) (-1) 2 65 w=(1)*w 146 + (2)*w 160 + (1)*w 179
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_201

theorem link0_202 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 66 w=rows0 w 202 := by
  change jetBlockRow (-1) (-1) 2 66 w=(1)*w 138 + (2)*w 144 + (1)*w 171
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_202

theorem link0_203 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 2 67 w=rows0 w 203 := by
  change jetBlockRow (-1) (-1) 2 67 w=(1)*w 160 + (2)*w 188 + (1)*w 193
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_203

theorem link0_204 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 0 w=rows0 w 204 := by
  change jetBlockRow (-1) (-1) 3 0 w=(11/3)*w 63 + (1/2)*w 129 + (1/22)*w 195 + (1)*w 198 + (1/484)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_204

theorem link0_205 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 1 w=rows0 w 205 := by
  change jetBlockRow (-1) (-1) 3 1 w=(242)*w 0 + (2178)*w 66 + (13068)*w 132 + (39204)*w 198 + (1)*w 199
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_205

theorem link0_206 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 2 w=rows0 w 206 := by
  change jetBlockRow (-1) (-1) 3 2 w=(242/3)*w 0 + (242)*w 66 + (484)*w 132 + (484)*w 198 + (1)*w 201
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_206

theorem link0_207 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 3 w=rows0 w 207 := by
  change jetBlockRow (-1) (-1) 3 3 w=((-242))*w 0 + (2178)*w 66 + ((-13068))*w 132 + (39204)*w 198 + (1)*w 263
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_207

theorem link0_208 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 4 w=rows0 w 208 := by
  change jetBlockRow (-1) (-1) 3 4 w=(166375/9)*w 65 + ((-3025)/18)*w 131 + (55/54)*w 197 + (1)*w 228 + ((-1)/324)*w 263
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_208

theorem link0_209 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 5 w=rows0 w 209 := by
  change jetBlockRow (-1) (-1) 3 5 w=(332750/3)*w 0 + ((-6050))*w 66 + (220)*w 132 + ((-4))*w 198 + (1)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_209

theorem link0_210 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 6 w=rows0 w 210 := by
  change jetBlockRow (-1) (-1) 3 6 w=(22/9)*w 64 + (2/9)*w 130 + (4/297)*w 196 + (1)*w 231 + (4/9801)*w 262
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_210

theorem link0_211 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 7 w=rows0 w 211 := by
  change jetBlockRow (-1) (-1) 3 7 w=(121)*w 33 + (1089/2)*w 99 + (3267/2)*w 165 + (1)*w 200 + (9801/4)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_211

theorem link0_212 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 8 w=rows0 w 212 := by
  change jetBlockRow (-1) (-1) 3 8 w=(121/3)*w 33 + (121/2)*w 99 + (121/2)*w 165 + (1)*w 204 + (121/4)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_212

theorem link0_213 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 9 w=rows0 w 213 := by
  change jetBlockRow (-1) (-1) 3 9 w=(22/3)*w 60 + (2)*w 126 + (4/11)*w 192 + (1)*w 231 + (4/121)*w 258
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_213

theorem link0_214 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 10 w=rows0 w 214 := by
  change jetBlockRow (-1) (-1) 3 10 w=((-166375))*w 63 + ((-27225)/2)*w 129 + ((-1485)/2)*w 195 + (1)*w 232 + ((-81)/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_214

theorem link0_215 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 11 w=rows0 w 215 := by
  change jetBlockRow (-1) (-1) 3 11 w=(11979)*w 65 + ((-1089)/2)*w 131 + (33/2)*w 197 + (1)*w 230 + ((-1)/4)*w 263
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_215

theorem link0_216 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 12 w=rows0 w 216 := by
  change jetBlockRow (-1) (-1) 3 12 w=((-11979))*w 63 + ((-1089)/2)*w 129 + ((-33)/2)*w 195 + (1)*w 234 + ((-1)/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_216

theorem link0_217 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 13 w=rows0 w 217 := by
  change jetBlockRow (-1) (-1) 3 13 w=(242/9)*w 44 + (242/9)*w 110 + (484/27)*w 176 + (1)*w 207 + (484/81)*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_217

theorem link0_218 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 14 w=rows0 w 218 := by
  change jetBlockRow (-1) (-1) 3 14 w=(22)*w 48 + (18)*w 114 + (108/11)*w 180 + (1)*w 209 + (324/121)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_218

theorem link0_219 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 15 w=rows0 w 219 := by
  change jetBlockRow (-1) (-1) 3 15 w=(121/9)*w 55 + (121/18)*w 121 + (121/54)*w 187 + (1)*w 216 + (121/324)*w 253
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_219

theorem link0_220 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 16 w=rows0 w 220 := by
  change jetBlockRow (-1) (-1) 3 16 w=(11)*w 57 + (9/2)*w 123 + (27/22)*w 189 + (1)*w 220 + (81/484)*w 255
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_220

theorem link0_221 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 17 w=rows0 w 221 := by
  change jetBlockRow (-1) (-1) 3 17 w=(5324/9)*w 4 + ((-242)/9)*w 70 + (22/27)*w 136 + ((-1)/81)*w 202 + (1)*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_221

theorem link0_222 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 18 w=rows0 w 222 := by
  change jetBlockRow (-1) (-1) 3 18 w=(5324)*w 12 + ((-2178))*w 78 + (594)*w 144 + ((-81))*w 210 + (1)*w 260
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_222

theorem link0_223 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 19 w=rows0 w 223 := by
  change jetBlockRow (-1) (-1) 3 19 w=((-23958))*w 62 + ((-2178))*w 128 + ((-132))*w 194 + (1)*w 233 + ((-4))*w 260
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_223

theorem link0_224 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 20 w=rows0 w 224 := by
  change jetBlockRow (-1) (-1) 3 20 w=(1331/9)*w 61 + ((-121)/18)*w 127 + (11/54)*w 193 + (1)*w 216 + ((-1)/324)*w 259
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_224

theorem link0_225 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 21 w=rows0 w 225 := by
  change jetBlockRow (-1) (-1) 3 21 w=(2662/9)*w 62 + ((-242)/9)*w 128 + (44/27)*w 194 + (1)*w 225 + ((-4)/81)*w 260
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_225

theorem link0_226 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 22 w=rows0 w 226 := by
  change jetBlockRow (-1) (-1) 3 22 w=((-2662))*w 42 + ((-2178))*w 108 + ((-1188))*w 174 + (1)*w 235 + ((-324))*w 240
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_226

theorem link0_227 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 23 w=rows0 w 227 := by
  change jetBlockRow (-1) (-1) 3 23 w=((-1331))*w 51 + ((-1089)/2)*w 117 + ((-297)/2)*w 183 + (1)*w 236 + ((-81)/4)*w 249
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_227

theorem link0_228 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 24 w=rows0 w 228 := by
  change jetBlockRow (-1) (-1) 3 24 w=((-2662)/3)*w 54 + ((-242))*w 120 + ((-44))*w 186 + (1)*w 237 + ((-4))*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_228

theorem link0_229 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 25 w=rows0 w 229 := by
  change jetBlockRow (-1) (-1) 3 25 w=((-1331)/3)*w 57 + ((-121)/2)*w 123 + ((-11)/2)*w 189 + (1)*w 240 + ((-1)/4)*w 255
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_229

theorem link0_230 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 26 w=rows0 w 230 := by
  change jetBlockRow (-1) (-1) 3 26 w=((-2662)/9)*w 58 + ((-242)/9)*w 124 + ((-44)/27)*w 190 + (1)*w 243 + ((-4)/81)*w 256
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_230

theorem link0_231 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 27 w=rows0 w 231 := by
  change jetBlockRow (-1) (-1) 3 27 w=((-1331)/9)*w 59 + ((-121)/18)*w 125 + ((-11)/54)*w 191 + (1)*w 252 + ((-1)/324)*w 257
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_231

theorem link0_232 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 28 w=rows0 w 232 := by
  change jetBlockRow (-1) (-1) 3 28 w=(1331/9)*w 7 + ((-121)/18)*w 73 + (11/54)*w 139 + ((-1)/324)*w 205 + (1)*w 210
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_232

theorem link0_233 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 29 w=rows0 w 233 := by
  change jetBlockRow (-1) (-1) 3 29 w=(2662/9)*w 8 + ((-242)/9)*w 74 + (44/27)*w 140 + ((-4)/81)*w 206 + (1)*w 219
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_233

theorem link0_234 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 30 w=rows0 w 234 := by
  change jetBlockRow (-1) (-1) 3 30 w=(1331/3)*w 9 + ((-121)/2)*w 75 + (11/2)*w 141 + ((-1)/4)*w 207 + (1)*w 222
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_234

theorem link0_235 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 31 w=rows0 w 235 := by
  change jetBlockRow (-1) (-1) 3 31 w=(1331)*w 15 + ((-1089)/2)*w 81 + (297/2)*w 147 + ((-81)/4)*w 213 + (1)*w 226
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_235

theorem link0_236 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 32 w=rows0 w 236 := by
  change jetBlockRow (-1) (-1) 3 32 w=(2662)*w 24 + ((-2178))*w 90 + (1188)*w 156 + ((-324))*w 222 + (1)*w 227
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_236

theorem link0_237 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 33 w=rows0 w 237 := by
  change jetBlockRow (-1) (-1) 3 33 w=((-2662))*w 54 + ((-2178))*w 120 + ((-1188))*w 186 + (1)*w 229 + ((-324))*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_237

theorem link0_238 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 34 w=rows0 w 238 := by
  change jetBlockRow (-1) (-1) 3 34 w=((-1331)/9)*w 5 + ((-121)/18)*w 71 + ((-11)/54)*w 137 + ((-1)/324)*w 203 + (1)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_238

theorem link0_239 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 35 w=rows0 w 239 := by
  change jetBlockRow (-1) (-1) 3 35 w=(1089)*w 11 + (1089)*w 33 + (1089/2)*w 77 + (1089/2)*w 99 + (363/2)*w 143 + (363/2)*w 165 + (121/4)*w 209 + (1)*w 222 + (121/4)*w 231 + (1)*w 244
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_239

theorem link0_240 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 36 w=rows0 w 240 := by
  change jetBlockRow (-1) (-1) 3 36 w=((-1089))*w 33 + ((-1089))*w 55 + (1089/2)*w 99 + (1089/2)*w 121 + ((-363)/2)*w 165 + ((-363)/2)*w 187 + (1)*w 218 + (121/4)*w 231 + (1)*w 240 + (121/4)*w 253
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_240

theorem link0_241 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 37 w=rows0 w 241 := by
  change jetBlockRow (-1) (-1) 3 37 w=(2662/3)*w 0 + (2662/3)*w 6 + (2662/3)*w 12 + (2662/3)*w 18 + (2662/3)*w 24 + (2662/3)*w 30 + (2662/3)*w 36 + (2662/3)*w 42 + (2662/3)*w 48 + (2662/3)*w 54 + (242)*w 66 + (242)*w 72 + (242)*w 78 + (242)*w 84 + (242)*w 90 + (242)*w 96 + (242)*w 102 + (242)*w 108 + (242)*w 114 + (242)*w 120 + (44)*w 132 + (44)*w 138 + (44)*w 144 + (44)*w 150 + (44)*w 156 + (44)*w 162 + (44)*w 168 + (44)*w 174 + (44)*w 180 + (44)*w 186 + (4)*w 198 + (4)*w 204 + (1)*w 207 + (4)*w 210 + (1)*w 213 + (4)*w 216 + (1)*w 219 + (4)*w 222 + (1)*w 225 + (4)*w 228 + (1)*w 231 + (4)*w 234 + (1)*w 237 + (4)*w 240 + (1)*w 243 + (4)*w 246 + (1)*w 249 + (4)*w 252 + (1)*w 255 + (1)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_241

theorem link0_242 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 38 w=rows0 w 242 := by
  change jetBlockRow (-1) (-1) 3 38 w=((-4356))*w 0 + ((-4356))*w 22 + (2178)*w 66 + (2178)*w 88 + ((-726))*w 132 + ((-726))*w 154 + (121)*w 198 + (1)*w 208 + (121)*w 220 + (1)*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_242

theorem link0_243 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 39 w=rows0 w 243 := by
  change jetBlockRow (-1) (-1) 3 39 w=(4356)*w 0 + (4356)*w 44 + (2178)*w 66 + (2178)*w 110 + (726)*w 132 + (726)*w 176 + (121)*w 198 + (1)*w 210 + (121)*w 242 + (1)*w 254
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_243

theorem link0_244 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 40 w=rows0 w 244 := by
  change jetBlockRow (-1) (-1) 3 40 w=(2178)*w 0 + (2178)*w 22 + (2178)*w 66 + (2178)*w 88 + (1452)*w 132 + (1452)*w 154 + (484)*w 198 + (484)*w 220 + (1)*w 221 + (1)*w 243
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_244

theorem link0_245 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 41 w=rows0 w 245 := by
  change jetBlockRow (-1) (-1) 3 41 w=((-2178))*w 0 + ((-2178))*w 44 + (2178)*w 66 + (2178)*w 110 + ((-1452))*w 132 + ((-1452))*w 176 + (484)*w 198 + (1)*w 219 + (1)*w 241 + (484)*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_245

theorem link0_246 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 42 w=rows0 w 246 := by
  change jetBlockRow (-1) (-1) 3 42 w=(2662)*w 0 + (2662)*w 6 + (2662)*w 12 + (2662)*w 18 + (2662)*w 24 + (2662)*w 30 + (2662)*w 36 + (2662)*w 42 + (2662)*w 54 + (2662)*w 60 + (2178)*w 66 + (2178)*w 72 + (2178)*w 78 + (2178)*w 84 + (2178)*w 90 + (2178)*w 96 + (2178)*w 102 + (2178)*w 108 + (2178)*w 120 + (2178)*w 126 + (1188)*w 132 + (1188)*w 138 + (1188)*w 144 + (1188)*w 150 + (1188)*w 156 + (1188)*w 162 + (1188)*w 168 + (1188)*w 174 + (1188)*w 186 + (1188)*w 192 + (324)*w 198 + (324)*w 204 + (1)*w 205 + (324)*w 210 + (1)*w 211 + (324)*w 216 + (1)*w 217 + (324)*w 222 + (1)*w 223 + (324)*w 228 + (1)*w 229 + (324)*w 234 + (1)*w 235 + (324)*w 240 + (1)*w 241 + (1)*w 247 + (324)*w 252 + (1)*w 253 + (324)*w 258 + (1)*w 259
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_246

theorem link0_247 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 43 w=rows0 w 247 := by
  change jetBlockRow (-1) (-1) 3 43 w=((-1331))*w 3 + ((-1331))*w 15 + ((-1331))*w 21 + ((-1331))*w 27 + ((-1331))*w 33 + ((-1331))*w 39 + ((-1331))*w 45 + ((-1331))*w 51 + ((-1331))*w 57 + ((-1331))*w 63 + (1089/2)*w 69 + (1089/2)*w 81 + (1089/2)*w 87 + (1089/2)*w 93 + (1089/2)*w 99 + (1089/2)*w 105 + (1089/2)*w 111 + (1089/2)*w 117 + (1089/2)*w 123 + (1089/2)*w 129 + ((-297)/2)*w 135 + ((-297)/2)*w 147 + ((-297)/2)*w 153 + ((-297)/2)*w 159 + ((-297)/2)*w 165 + ((-297)/2)*w 171 + ((-297)/2)*w 177 + ((-297)/2)*w 183 + ((-297)/2)*w 189 + ((-297)/2)*w 195 + (81/4)*w 201 + (1)*w 202 + (1)*w 208 + (81/4)*w 213 + (1)*w 214 + (81/4)*w 219 + (1)*w 220 + (81/4)*w 225 + (1)*w 226 + (81/4)*w 231 + (1)*w 232 + (81/4)*w 237 + (1)*w 238 + (81/4)*w 243 + (1)*w 244 + (81/4)*w 249 + (1)*w 250 + (81/4)*w 255 + (1)*w 256 + (81/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_247

theorem link0_248 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 44 w=rows0 w 248 := by
  change jetBlockRow (-1) (-1) 3 44 w=(1331)*w 3 + (1331)*w 9 + (1331)*w 15 + (1331)*w 21 + (1331)*w 27 + (1331)*w 33 + (1331)*w 39 + (1331)*w 45 + (1331)*w 51 + (1331)*w 63 + (1089/2)*w 69 + (1089/2)*w 75 + (1089/2)*w 81 + (1089/2)*w 87 + (1089/2)*w 93 + (1089/2)*w 99 + (1089/2)*w 105 + (1089/2)*w 111 + (1089/2)*w 117 + (1089/2)*w 129 + (297/2)*w 135 + (297/2)*w 141 + (297/2)*w 147 + (297/2)*w 153 + (297/2)*w 159 + (297/2)*w 165 + (297/2)*w 171 + (297/2)*w 177 + (297/2)*w 183 + (297/2)*w 195 + (81/4)*w 201 + (1)*w 206 + (81/4)*w 207 + (1)*w 212 + (81/4)*w 213 + (1)*w 218 + (81/4)*w 219 + (1)*w 224 + (81/4)*w 225 + (1)*w 230 + (81/4)*w 231 + (1)*w 236 + (81/4)*w 237 + (1)*w 242 + (81/4)*w 243 + (1)*w 248 + (81/4)*w 249 + (1)*w 254 + (1)*w 260 + (81/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_248

theorem link0_249 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 45 w=rows0 w 249 := by
  change jetBlockRow (-1) (-1) 3 45 w=((-2662))*w 0 + ((-2662))*w 6 + ((-2662))*w 12 + ((-2662))*w 24 + ((-2662))*w 30 + ((-2662))*w 36 + ((-2662))*w 42 + ((-2662))*w 48 + ((-2662))*w 54 + ((-2662))*w 60 + (2178)*w 66 + (2178)*w 72 + (2178)*w 78 + (2178)*w 90 + (2178)*w 96 + (2178)*w 102 + (2178)*w 108 + (2178)*w 114 + (2178)*w 120 + (2178)*w 126 + ((-1188))*w 132 + ((-1188))*w 138 + ((-1188))*w 144 + ((-1188))*w 156 + ((-1188))*w 162 + ((-1188))*w 168 + ((-1188))*w 174 + ((-1188))*w 180 + ((-1188))*w 186 + ((-1188))*w 192 + (324)*w 198 + (1)*w 203 + (324)*w 204 + (1)*w 209 + (324)*w 210 + (1)*w 215 + (1)*w 221 + (324)*w 222 + (1)*w 227 + (324)*w 228 + (1)*w 233 + (324)*w 234 + (1)*w 239 + (324)*w 240 + (1)*w 245 + (324)*w 246 + (1)*w 251 + (324)*w 252 + (1)*w 257 + (324)*w 258
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_249

theorem link0_250 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 46 w=rows0 w 250 := by
  change jetBlockRow (-1) (-1) 3 46 w=(1)*w 198
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_250

theorem link0_251 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 47 w=rows0 w 251 := by
  change jetBlockRow (-1) (-1) 3 47 w=(1)*w 220 + (1)*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_251

theorem link0_252 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 48 w=rows0 w 252 := by
  change jetBlockRow (-1) (-1) 3 48 w=(1)*w 209 + (1)*w 253
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_252

theorem link0_253 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 49 w=rows0 w 253 := by
  change jetBlockRow (-1) (-1) 3 49 w=(1)*w 204 + (1)*w 210 + (1)*w 216 + (1)*w 222 + (1)*w 228 + (1)*w 234 + (1)*w 240 + (1)*w 246 + (1)*w 252 + (1)*w 258
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_253

theorem link0_254 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 50 w=rows0 w 254 := by
  change jetBlockRow (-1) (-1) 3 50 w=(1)*w 207 + (4)*w 216 + (1)*w 240
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_254

theorem link0_255 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 51 w=rows0 w 255 := by
  change jetBlockRow (-1) (-1) 3 51 w=(1)*w 213 + (4)*w 228 + (1)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_255

theorem link0_256 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 52 w=rows0 w 256 := by
  change jetBlockRow (-1) (-1) 3 52 w=(1)*w 214 + (4)*w 230 + (1)*w 247
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_256

theorem link0_257 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 53 w=rows0 w 257 := by
  change jetBlockRow (-1) (-1) 3 53 w=(1)*w 215 + (4)*w 232 + (1)*w 248
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_257

theorem link0_258 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 54 w=rows0 w 258 := by
  change jetBlockRow (-1) (-1) 3 54 w=(1)*w 216 + (4)*w 234 + (1)*w 249
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_258

theorem link0_259 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 55 w=rows0 w 259 := by
  change jetBlockRow (-1) (-1) 3 55 w=(1)*w 203 + (4)*w 208 + (1)*w 236
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_259

theorem link0_260 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 56 w=rows0 w 260 := by
  change jetBlockRow (-1) (-1) 3 56 w=(1)*w 202 + (4)*w 206 + (1)*w 235
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_260

theorem link0_261 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 57 w=rows0 w 261 := by
  change jetBlockRow (-1) (-1) 3 57 w=(1)*w 205 + (21)*w 219 + (1)*w 227 + (1)*w 249 + (81)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_261

theorem link0_262 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 58 w=rows0 w 262 := by
  change jetBlockRow (-1) (-1) 3 58 w=(1)*w 202 + (21)*w 210 + (1)*w 224 + (81)*w 234 + (1)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_262

theorem link0_263 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 59 w=rows0 w 263 := by
  change jetBlockRow (-1) (-1) 3 59 w=(1)*w 211 + (4)*w 224 + (1)*w 244
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_263

theorem link0_264 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 60 w=rows0 w 264 := by
  change jetBlockRow (-1) (-1) 3 60 w=(1)*w 224 + (4)*w 250 + (1)*w 257
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_264

theorem link0_265 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 61 w=rows0 w 265 := by
  change jetBlockRow (-1) (-1) 3 61 w=(1)*w 217 + (4)*w 236 + (1)*w 250
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_265

theorem link0_266 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 62 w=rows0 w 266 := by
  change jetBlockRow (-1) (-1) 3 62 w=(1)*w 203 + (21)*w 213 + (1)*w 225 + (81)*w 243 + (1)*w 247
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_266

theorem link0_267 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 63 w=rows0 w 267 := by
  change jetBlockRow (-1) (-1) 3 63 w=(1)*w 205 + (4)*w 212 + (1)*w 238
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_267

theorem link0_268 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 64 w=rows0 w 268 := by
  change jetBlockRow (-1) (-1) 3 64 w=(1)*w 206 + (4)*w 214 + (1)*w 239
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_268

theorem link0_269 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 65 w=rows0 w 269 := by
  change jetBlockRow (-1) (-1) 3 65 w=(1)*w 212 + (4)*w 226 + (1)*w 245
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_269

theorem link0_270 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 66 w=rows0 w 270 := by
  change jetBlockRow (-1) (-1) 3 66 w=(1)*w 204 + (4)*w 210 + (1)*w 237
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_270

theorem link0_271 (w : Fin 264→ℂ) : jetBlockRow (-1) (-1) 3 67 w=rows0 w 271 := by
  change jetBlockRow (-1) (-1) 3 67 w=(1)*w 226 + (4)*w 254 + (1)*w 259
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_271

end SmallLevelTwentyTwoJetBlock
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoJetBlock
open Complex SmallLevelFiniteShift SmallLevelTwentyTwoLaurent SmallLevelTwentyTwoThirdJet

theorem link1_0 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 0 w=rows1 w 0 := by
  change jetBlockRow (-1) (1) 0 0 w=(1)*w 0 + (22)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_0

theorem link1_1 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 1 w=rows1 w 1 := by
  change jetBlockRow (-1) (1) 0 1 w=(1/198)*w 0 + (1)*w 1
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_1

theorem link1_2 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 2 w=rows1 w 2 := by
  change jetBlockRow (-1) (1) 0 2 w=(1/22)*w 0 + (1)*w 3
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_2

theorem link1_3 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 3 w=rows1 w 3 := by
  change jetBlockRow (-1) (1) 0 3 w=(1/198)*w 0 + (1)*w 65
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_3

theorem link1_4 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 4 w=rows1 w 4 := by
  change jetBlockRow (-1) (1) 0 4 w=(1)*w 30 + ((-18))*w 65
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_4

theorem link1_5 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 5 w=rows1 w 5 := by
  change jetBlockRow (-1) (1) 0 5 w=((-1)/2)*w 0 + (1)*w 33
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_5

theorem link1_6 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 6 w=rows1 w 6 := by
  change jetBlockRow (-1) (1) 0 6 w=(1)*w 33 + (99/2)*w 64
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_6

theorem link1_7 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 7 w=rows1 w 7 := by
  change jetBlockRow (-1) (1) 0 7 w=(1)*w 2 + (2/99)*w 33
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_7

theorem link1_8 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 8 w=rows1 w 8 := by
  change jetBlockRow (-1) (1) 0 8 w=(1)*w 6 + (2/11)*w 33
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_8

theorem link1_9 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 9 w=rows1 w 9 := by
  change jetBlockRow (-1) (1) 0 9 w=(1)*w 33 + (11/2)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_9

theorem link1_10 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 10 w=rows1 w 10 := by
  change jetBlockRow (-1) (1) 0 10 w=(1)*w 34 + ((-2)/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_10

theorem link1_11 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 11 w=rows1 w 11 := by
  change jetBlockRow (-1) (1) 0 11 w=(1)*w 32 + ((-2))*w 65
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_11

theorem link1_12 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 12 w=rows1 w 12 := by
  change jetBlockRow (-1) (1) 0 12 w=(1)*w 36 + ((-2))*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_12

theorem link1_13 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 13 w=rows1 w 13 := by
  change jetBlockRow (-1) (1) 0 13 w=(1)*w 9 + (9/22)*w 44
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_13

theorem link1_14 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 14 w=rows1 w 14 := by
  change jetBlockRow (-1) (1) 0 14 w=(1)*w 11 + (11/18)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_14

theorem link1_15 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 15 w=rows1 w 15 := by
  change jetBlockRow (-1) (1) 0 15 w=(1)*w 18 + (18/11)*w 55
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_15

theorem link1_16 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 16 w=rows1 w 16 := by
  change jetBlockRow (-1) (1) 0 16 w=(1)*w 22 + (22/9)*w 57
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_16

theorem link1_17 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 17 w=rows1 w 17 := by
  change jetBlockRow (-1) (1) 0 17 w=((-9))*w 4 + (1)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_17

theorem link1_18 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 18 w=rows1 w 18 := by
  change jetBlockRow (-1) (1) 0 18 w=((-1)/9)*w 12 + (1)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_18

theorem link1_19 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 19 w=rows1 w 19 := by
  change jetBlockRow (-1) (1) 0 19 w=(1)*w 35 + ((-1)/2)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_19

theorem link1_20 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 20 w=rows1 w 20 := by
  change jetBlockRow (-1) (1) 0 20 w=(1)*w 18 + ((-18))*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_20

theorem link1_21 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 21 w=rows1 w 21 := by
  change jetBlockRow (-1) (1) 0 21 w=(1)*w 27 + ((-9)/2)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_21

theorem link1_22 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 22 w=rows1 w 22 := by
  change jetBlockRow (-1) (1) 0 22 w=(1)*w 37 + ((-1)/18)*w 42
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_22

theorem link1_23 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 23 w=rows1 w 23 := by
  change jetBlockRow (-1) (1) 0 23 w=(1)*w 38 + ((-2)/9)*w 51
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_23

theorem link1_24 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 24 w=rows1 w 24 := by
  change jetBlockRow (-1) (1) 0 24 w=(1)*w 39 + ((-1)/2)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_24

theorem link1_25 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 25 w=rows1 w 25 := by
  change jetBlockRow (-1) (1) 0 25 w=(1)*w 42 + ((-2))*w 57
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_25

theorem link1_26 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 26 w=rows1 w 26 := by
  change jetBlockRow (-1) (1) 0 26 w=(1)*w 45 + ((-9)/2)*w 58
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_26

theorem link1_27 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 27 w=rows1 w 27 := by
  change jetBlockRow (-1) (1) 0 27 w=(1)*w 54 + ((-18))*w 59
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_27

theorem link1_28 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 28 w=rows1 w 28 := by
  change jetBlockRow (-1) (1) 0 28 w=((-18))*w 7 + (1)*w 12
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_28

theorem link1_29 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 29 w=rows1 w 29 := by
  change jetBlockRow (-1) (1) 0 29 w=((-9)/2)*w 8 + (1)*w 21
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_29

theorem link1_30 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 30 w=rows1 w 30 := by
  change jetBlockRow (-1) (1) 0 30 w=((-2))*w 9 + (1)*w 24
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_30

theorem link1_31 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 31 w=rows1 w 31 := by
  change jetBlockRow (-1) (1) 0 31 w=((-2)/9)*w 15 + (1)*w 28
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_31

theorem link1_32 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 32 w=rows1 w 32 := by
  change jetBlockRow (-1) (1) 0 32 w=((-1)/18)*w 24 + (1)*w 29
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_32

theorem link1_33 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 33 w=rows1 w 33 := by
  change jetBlockRow (-1) (1) 0 33 w=(1)*w 31 + ((-1)/18)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_33

theorem link1_34 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 34 w=rows1 w 34 := by
  change jetBlockRow (-1) (1) 0 34 w=((-18))*w 5 + (1)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_34

theorem link1_35 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 35 w=rows1 w 35 := by
  change jetBlockRow (-1) (1) 0 35 w=(2/11)*w 11 + (1)*w 24 + (2/11)*w 33 + (1)*w 46
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_35

theorem link1_36 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 36 w=rows1 w 36 := by
  change jetBlockRow (-1) (1) 0 36 w=(1)*w 20 + (2/11)*w 33 + (1)*w 42 + (2/11)*w 55
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_36

theorem link1_37 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 37 w=rows1 w 37 := by
  change jetBlockRow (-1) (1) 0 37 w=((-1)/2)*w 0 + ((-1)/2)*w 6 + (1)*w 9 + ((-1)/2)*w 12 + (1)*w 15 + ((-1)/2)*w 18 + (1)*w 21 + ((-1)/2)*w 24 + (1)*w 27 + ((-1)/2)*w 30 + (1)*w 33 + ((-1)/2)*w 36 + (1)*w 39 + ((-1)/2)*w 42 + (1)*w 45 + ((-1)/2)*w 48 + (1)*w 51 + ((-1)/2)*w 54 + (1)*w 57 + (1)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_37

theorem link1_38 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 38 w=rows1 w 38 := by
  change jetBlockRow (-1) (1) 0 38 w=(1/11)*w 0 + (1)*w 10 + (1/11)*w 22 + (1)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_38

theorem link1_39 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 39 w=rows1 w 39 := by
  change jetBlockRow (-1) (1) 0 39 w=(1/11)*w 0 + (1)*w 12 + (1/11)*w 44 + (1)*w 56
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_39

theorem link1_40 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 40 w=rows1 w 40 := by
  change jetBlockRow (-1) (1) 0 40 w=(1/22)*w 0 + (1/22)*w 22 + (1)*w 23 + (1)*w 45
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_40

theorem link1_41 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 41 w=rows1 w 41 := by
  change jetBlockRow (-1) (1) 0 41 w=(1/22)*w 0 + (1)*w 21 + (1)*w 43 + (1/22)*w 44
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_41

theorem link1_42 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 42 w=rows1 w 42 := by
  change jetBlockRow (-1) (1) 0 42 w=((-1)/18)*w 0 + ((-1)/18)*w 6 + (1)*w 7 + ((-1)/18)*w 12 + (1)*w 13 + ((-1)/18)*w 18 + (1)*w 19 + ((-1)/18)*w 24 + (1)*w 25 + ((-1)/18)*w 30 + (1)*w 31 + ((-1)/18)*w 36 + (1)*w 37 + ((-1)/18)*w 42 + (1)*w 43 + (1)*w 49 + ((-1)/18)*w 54 + (1)*w 55 + ((-1)/18)*w 60 + (1)*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_42

theorem link1_43 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 43 w=rows1 w 43 := by
  change jetBlockRow (-1) (1) 0 43 w=((-2)/9)*w 3 + (1)*w 4 + (1)*w 10 + ((-2)/9)*w 15 + (1)*w 16 + ((-2)/9)*w 21 + (1)*w 22 + ((-2)/9)*w 27 + (1)*w 28 + ((-2)/9)*w 33 + (1)*w 34 + ((-2)/9)*w 39 + (1)*w 40 + ((-2)/9)*w 45 + (1)*w 46 + ((-2)/9)*w 51 + (1)*w 52 + ((-2)/9)*w 57 + (1)*w 58 + ((-2)/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_43

theorem link1_44 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 44 w=rows1 w 44 := by
  change jetBlockRow (-1) (1) 0 44 w=((-2)/9)*w 3 + (1)*w 8 + ((-2)/9)*w 9 + (1)*w 14 + ((-2)/9)*w 15 + (1)*w 20 + ((-2)/9)*w 21 + (1)*w 26 + ((-2)/9)*w 27 + (1)*w 32 + ((-2)/9)*w 33 + (1)*w 38 + ((-2)/9)*w 39 + (1)*w 44 + ((-2)/9)*w 45 + (1)*w 50 + ((-2)/9)*w 51 + (1)*w 56 + (1)*w 62 + ((-2)/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_44

theorem link1_45 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 45 w=rows1 w 45 := by
  change jetBlockRow (-1) (1) 0 45 w=((-1)/18)*w 0 + (1)*w 5 + ((-1)/18)*w 6 + (1)*w 11 + ((-1)/18)*w 12 + (1)*w 17 + (1)*w 23 + ((-1)/18)*w 24 + (1)*w 29 + ((-1)/18)*w 30 + (1)*w 35 + ((-1)/18)*w 36 + (1)*w 41 + ((-1)/18)*w 42 + (1)*w 47 + ((-1)/18)*w 48 + (1)*w 53 + ((-1)/18)*w 54 + (1)*w 59 + ((-1)/18)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_45

theorem link1_46 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 46 w=rows1 w 46 := by
  change jetBlockRow (-1) (1) 0 46 w=(1)*w 0
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_46

theorem link1_47 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 47 w=rows1 w 47 := by
  change jetBlockRow (-1) (1) 0 47 w=(1)*w 22 + (1)*w 44
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_47

theorem link1_48 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 48 w=rows1 w 48 := by
  change jetBlockRow (-1) (1) 0 48 w=(1)*w 11 + (1)*w 55
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_48

theorem link1_49 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 49 w=rows1 w 49 := by
  change jetBlockRow (-1) (1) 0 49 w=(1)*w 6 + (1)*w 12 + (1)*w 18 + (1)*w 24 + (1)*w 30 + (1)*w 36 + (1)*w 42 + (1)*w 48 + (1)*w 54 + (1)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_49

theorem link1_50 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 50 w=rows1 w 50 := by
  change jetBlockRow (-1) (1) 0 50 w=(1)*w 9 + (1/2)*w 18 + (1)*w 42
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_50

theorem link1_51 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 51 w=rows1 w 51 := by
  change jetBlockRow (-1) (1) 0 51 w=(1)*w 15 + (1/2)*w 30 + (1)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_51

theorem link1_52 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 52 w=rows1 w 52 := by
  change jetBlockRow (-1) (1) 0 52 w=(1)*w 16 + (1/2)*w 32 + (1)*w 49
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_52

theorem link1_53 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 53 w=rows1 w 53 := by
  change jetBlockRow (-1) (1) 0 53 w=(1)*w 17 + (1/2)*w 34 + (1)*w 50
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_53

theorem link1_54 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 54 w=rows1 w 54 := by
  change jetBlockRow (-1) (1) 0 54 w=(1)*w 18 + (1/2)*w 36 + (1)*w 51
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_54

theorem link1_55 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 55 w=rows1 w 55 := by
  change jetBlockRow (-1) (1) 0 55 w=(1)*w 5 + (1/2)*w 10 + (1)*w 38
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_55

theorem link1_56 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 56 w=rows1 w 56 := by
  change jetBlockRow (-1) (1) 0 56 w=(1)*w 4 + (1/2)*w 8 + (1)*w 37
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_56

theorem link1_57 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 57 w=rows1 w 57 := by
  change jetBlockRow (-1) (1) 0 57 w=(1)*w 7 + (7/9)*w 21 + (1)*w 29 + (1)*w 51 + (1/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_57

theorem link1_58 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 58 w=rows1 w 58 := by
  change jetBlockRow (-1) (1) 0 58 w=(1)*w 4 + (7/9)*w 12 + (1)*w 26 + (1/9)*w 36 + (1)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_58

theorem link1_59 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 59 w=rows1 w 59 := by
  change jetBlockRow (-1) (1) 0 59 w=(1)*w 13 + (1/2)*w 26 + (1)*w 46
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_59

theorem link1_60 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 60 w=rows1 w 60 := by
  change jetBlockRow (-1) (1) 0 60 w=(1)*w 26 + (1/2)*w 52 + (1)*w 59
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_60

theorem link1_61 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 61 w=rows1 w 61 := by
  change jetBlockRow (-1) (1) 0 61 w=(1)*w 19 + (1/2)*w 38 + (1)*w 52
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_61

theorem link1_62 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 62 w=rows1 w 62 := by
  change jetBlockRow (-1) (1) 0 62 w=(1)*w 5 + (7/9)*w 15 + (1)*w 27 + (1/9)*w 45 + (1)*w 49
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_62

theorem link1_63 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 63 w=rows1 w 63 := by
  change jetBlockRow (-1) (1) 0 63 w=(1)*w 7 + (1/2)*w 14 + (1)*w 40
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_63

theorem link1_64 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 64 w=rows1 w 64 := by
  change jetBlockRow (-1) (1) 0 64 w=(1)*w 8 + (1/2)*w 16 + (1)*w 41
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_64

theorem link1_65 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 65 w=rows1 w 65 := by
  change jetBlockRow (-1) (1) 0 65 w=(1)*w 14 + (1/2)*w 28 + (1)*w 47
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_65

theorem link1_66 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 66 w=rows1 w 66 := by
  change jetBlockRow (-1) (1) 0 66 w=(1)*w 6 + (1/2)*w 12 + (1)*w 39
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_66

theorem link1_67 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 0 67 w=rows1 w 67 := by
  change jetBlockRow (-1) (1) 0 67 w=(1)*w 28 + (1/2)*w 56 + (1)*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_67

theorem link1_68 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 0 w=rows1 w 68 := by
  change jetBlockRow (-1) (1) 1 0 w=(22)*w 63 + (1)*w 66 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_68

theorem link1_69 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 1 w=rows1 w 69 := by
  change jetBlockRow (-1) (1) 1 1 w=(1/3)*w 0 + (1)*w 66 + (1)*w 67
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_69

theorem link1_70 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 2 w=rows1 w 70 := by
  change jetBlockRow (-1) (1) 1 2 w=(1)*w 0 + (1)*w 66 + (1)*w 69
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_70

theorem link1_71 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 3 w=rows1 w 71 := by
  change jetBlockRow (-1) (1) 1 3 w=((-1)/3)*w 0 + (1)*w 66 + (1)*w 131
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_71

theorem link1_72 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 4 w=rows1 w 72 := by
  change jetBlockRow (-1) (1) 1 4 w=(330)*w 65 + (1)*w 96 + ((-1))*w 131
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_72

theorem link1_73 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 5 w=rows1 w 73 := by
  change jetBlockRow (-1) (1) 1 5 w=(55)*w 0 + ((-1))*w 66 + (1)*w 99
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_73

theorem link1_74 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 6 w=rows1 w 74 := by
  change jetBlockRow (-1) (1) 1 6 w=(33)*w 64 + (1)*w 99 + (1)*w 130
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_74

theorem link1_75 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 7 w=rows1 w 75 := by
  change jetBlockRow (-1) (1) 1 7 w=(2/3)*w 33 + (1)*w 68 + (1)*w 99
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_75

theorem link1_76 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 8 w=rows1 w 76 := by
  change jetBlockRow (-1) (1) 1 8 w=(2)*w 33 + (1)*w 72 + (1)*w 99
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_76

theorem link1_77 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 9 w=rows1 w 77 := by
  change jetBlockRow (-1) (1) 1 9 w=(11)*w 60 + (1)*w 99 + (1)*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_77

theorem link1_78 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 10 w=rows1 w 78 := by
  change jetBlockRow (-1) (1) 1 10 w=((-110)/3)*w 63 + (1)*w 100 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_78

theorem link1_79 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 11 w=rows1 w 79 := by
  change jetBlockRow (-1) (1) 1 11 w=(66)*w 65 + (1)*w 98 + ((-1))*w 131
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_79

theorem link1_80 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 12 w=rows1 w 80 := by
  change jetBlockRow (-1) (1) 1 12 w=((-66))*w 63 + (1)*w 102 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_80

theorem link1_81 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 13 w=rows1 w 81 := by
  change jetBlockRow (-1) (1) 1 13 w=(3)*w 44 + (1)*w 75 + (1)*w 110
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_81

theorem link1_82 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 14 w=rows1 w 82 := by
  change jetBlockRow (-1) (1) 1 14 w=(11/3)*w 48 + (1)*w 77 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_82

theorem link1_83 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 15 w=rows1 w 83 := by
  change jetBlockRow (-1) (1) 1 15 w=(6)*w 55 + (1)*w 84 + (1)*w 121
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_83

theorem link1_84 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 16 w=rows1 w 84 := by
  change jetBlockRow (-1) (1) 1 16 w=(22/3)*w 57 + (1)*w 88 + (1)*w 123
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_84

theorem link1_85 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 17 w=rows1 w 85 := by
  change jetBlockRow (-1) (1) 1 17 w=(66)*w 4 + ((-1))*w 70 + (1)*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_85

theorem link1_86 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 18 w=rows1 w 86 := by
  change jetBlockRow (-1) (1) 1 18 w=(22/3)*w 12 + ((-1))*w 78 + (1)*w 128
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_86

theorem link1_87 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 19 w=rows1 w 87 := by
  change jetBlockRow (-1) (1) 1 19 w=((-33))*w 62 + (1)*w 101 + ((-1))*w 128
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_87

theorem link1_88 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 20 w=rows1 w 88 := by
  change jetBlockRow (-1) (1) 1 20 w=(66)*w 61 + (1)*w 84 + ((-1))*w 127
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_88

theorem link1_89 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 21 w=rows1 w 89 := by
  change jetBlockRow (-1) (1) 1 21 w=(33)*w 62 + (1)*w 93 + ((-1))*w 128
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_89

theorem link1_90 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 22 w=rows1 w 90 := by
  change jetBlockRow (-1) (1) 1 22 w=((-11)/3)*w 42 + (1)*w 103 + ((-1))*w 108
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_90

theorem link1_91 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 23 w=rows1 w 91 := by
  change jetBlockRow (-1) (1) 1 23 w=((-22)/3)*w 51 + (1)*w 104 + ((-1))*w 117
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_91

theorem link1_92 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 24 w=rows1 w 92 := by
  change jetBlockRow (-1) (1) 1 24 w=((-11))*w 54 + (1)*w 105 + ((-1))*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_92

theorem link1_93 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 25 w=rows1 w 93 := by
  change jetBlockRow (-1) (1) 1 25 w=((-22))*w 57 + (1)*w 108 + ((-1))*w 123
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_93

theorem link1_94 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 26 w=rows1 w 94 := by
  change jetBlockRow (-1) (1) 1 26 w=((-33))*w 58 + (1)*w 111 + ((-1))*w 124
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_94

theorem link1_95 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 27 w=rows1 w 95 := by
  change jetBlockRow (-1) (1) 1 27 w=((-66))*w 59 + (1)*w 120 + ((-1))*w 125
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_95

theorem link1_96 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 28 w=rows1 w 96 := by
  change jetBlockRow (-1) (1) 1 28 w=(66)*w 7 + ((-1))*w 73 + (1)*w 78
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_96

theorem link1_97 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 29 w=rows1 w 97 := by
  change jetBlockRow (-1) (1) 1 29 w=(33)*w 8 + ((-1))*w 74 + (1)*w 87
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_97

theorem link1_98 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 30 w=rows1 w 98 := by
  change jetBlockRow (-1) (1) 1 30 w=(22)*w 9 + ((-1))*w 75 + (1)*w 90
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_98

theorem link1_99 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 31 w=rows1 w 99 := by
  change jetBlockRow (-1) (1) 1 31 w=(22/3)*w 15 + ((-1))*w 81 + (1)*w 94
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_99

theorem link1_100 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 32 w=rows1 w 100 := by
  change jetBlockRow (-1) (1) 1 32 w=(11/3)*w 24 + ((-1))*w 90 + (1)*w 95
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_100

theorem link1_101 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 33 w=rows1 w 101 := by
  change jetBlockRow (-1) (1) 1 33 w=((-11)/3)*w 54 + (1)*w 97 + ((-1))*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_101

theorem link1_102 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 34 w=rows1 w 102 := by
  change jetBlockRow (-1) (1) 1 34 w=((-66))*w 5 + ((-1))*w 71 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_102

theorem link1_103 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 35 w=rows1 w 103 := by
  change jetBlockRow (-1) (1) 1 35 w=(6)*w 11 + (6)*w 33 + (1)*w 77 + (1)*w 90 + (1)*w 99 + (1)*w 112
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_103

theorem link1_104 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 36 w=rows1 w 104 := by
  change jetBlockRow (-1) (1) 1 36 w=((-6))*w 33 + ((-6))*w 55 + (1)*w 86 + (1)*w 99 + (1)*w 108 + (1)*w 121
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_104

theorem link1_105 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 37 w=rows1 w 105 := by
  change jetBlockRow (-1) (1) 1 37 w=((-11))*w 0 + ((-11))*w 6 + ((-11))*w 12 + ((-11))*w 18 + ((-11))*w 24 + ((-11))*w 30 + ((-11))*w 36 + ((-11))*w 42 + ((-11))*w 48 + ((-11))*w 54 + ((-1))*w 66 + ((-1))*w 72 + (1)*w 75 + ((-1))*w 78 + (1)*w 81 + ((-1))*w 84 + (1)*w 87 + ((-1))*w 90 + (1)*w 93 + ((-1))*w 96 + (1)*w 99 + ((-1))*w 102 + (1)*w 105 + ((-1))*w 108 + (1)*w 111 + ((-1))*w 114 + (1)*w 117 + ((-1))*w 120 + (1)*w 123 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_105

theorem link1_106 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 38 w=rows1 w 106 := by
  change jetBlockRow (-1) (1) 1 38 w=((-6))*w 0 + ((-6))*w 22 + (1)*w 66 + (1)*w 76 + (1)*w 88 + (1)*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_106

theorem link1_107 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 39 w=rows1 w 107 := by
  change jetBlockRow (-1) (1) 1 39 w=(6)*w 0 + (6)*w 44 + (1)*w 66 + (1)*w 78 + (1)*w 110 + (1)*w 122
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_107

theorem link1_108 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 40 w=rows1 w 108 := by
  change jetBlockRow (-1) (1) 1 40 w=(3)*w 0 + (3)*w 22 + (1)*w 66 + (1)*w 88 + (1)*w 89 + (1)*w 111
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_108

theorem link1_109 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 41 w=rows1 w 109 := by
  change jetBlockRow (-1) (1) 1 41 w=((-3))*w 0 + ((-3))*w 44 + (1)*w 66 + (1)*w 87 + (1)*w 109 + (1)*w 110
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_109

theorem link1_110 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 42 w=rows1 w 110 := by
  change jetBlockRow (-1) (1) 1 42 w=((-11)/3)*w 0 + ((-11)/3)*w 6 + ((-11)/3)*w 12 + ((-11)/3)*w 18 + ((-11)/3)*w 24 + ((-11)/3)*w 30 + ((-11)/3)*w 36 + ((-11)/3)*w 42 + ((-11)/3)*w 54 + ((-11)/3)*w 60 + ((-1))*w 66 + ((-1))*w 72 + (1)*w 73 + ((-1))*w 78 + (1)*w 79 + ((-1))*w 84 + (1)*w 85 + ((-1))*w 90 + (1)*w 91 + ((-1))*w 96 + (1)*w 97 + ((-1))*w 102 + (1)*w 103 + ((-1))*w 108 + (1)*w 109 + (1)*w 115 + ((-1))*w 120 + (1)*w 121 + ((-1))*w 126 + (1)*w 127
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_110

theorem link1_111 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 43 w=rows1 w 111 := by
  change jetBlockRow (-1) (1) 1 43 w=(22/3)*w 3 + (22/3)*w 15 + (22/3)*w 21 + (22/3)*w 27 + (22/3)*w 33 + (22/3)*w 39 + (22/3)*w 45 + (22/3)*w 51 + (22/3)*w 57 + (22/3)*w 63 + ((-1))*w 69 + (1)*w 70 + (1)*w 76 + ((-1))*w 81 + (1)*w 82 + ((-1))*w 87 + (1)*w 88 + ((-1))*w 93 + (1)*w 94 + ((-1))*w 99 + (1)*w 100 + ((-1))*w 105 + (1)*w 106 + ((-1))*w 111 + (1)*w 112 + ((-1))*w 117 + (1)*w 118 + ((-1))*w 123 + (1)*w 124 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_111

theorem link1_112 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 44 w=rows1 w 112 := by
  change jetBlockRow (-1) (1) 1 44 w=((-22)/3)*w 3 + ((-22)/3)*w 9 + ((-22)/3)*w 15 + ((-22)/3)*w 21 + ((-22)/3)*w 27 + ((-22)/3)*w 33 + ((-22)/3)*w 39 + ((-22)/3)*w 45 + ((-22)/3)*w 51 + ((-22)/3)*w 63 + ((-1))*w 69 + (1)*w 74 + ((-1))*w 75 + (1)*w 80 + ((-1))*w 81 + (1)*w 86 + ((-1))*w 87 + (1)*w 92 + ((-1))*w 93 + (1)*w 98 + ((-1))*w 99 + (1)*w 104 + ((-1))*w 105 + (1)*w 110 + ((-1))*w 111 + (1)*w 116 + ((-1))*w 117 + (1)*w 122 + (1)*w 128 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_112

theorem link1_113 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 45 w=rows1 w 113 := by
  change jetBlockRow (-1) (1) 1 45 w=(11/3)*w 0 + (11/3)*w 6 + (11/3)*w 12 + (11/3)*w 24 + (11/3)*w 30 + (11/3)*w 36 + (11/3)*w 42 + (11/3)*w 48 + (11/3)*w 54 + (11/3)*w 60 + ((-1))*w 66 + (1)*w 71 + ((-1))*w 72 + (1)*w 77 + ((-1))*w 78 + (1)*w 83 + (1)*w 89 + ((-1))*w 90 + (1)*w 95 + ((-1))*w 96 + (1)*w 101 + ((-1))*w 102 + (1)*w 107 + ((-1))*w 108 + (1)*w 113 + ((-1))*w 114 + (1)*w 119 + ((-1))*w 120 + (1)*w 125 + ((-1))*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_113

theorem link1_114 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 46 w=rows1 w 114 := by
  change jetBlockRow (-1) (1) 1 46 w=(1)*w 66
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_114

theorem link1_115 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 47 w=rows1 w 115 := by
  change jetBlockRow (-1) (1) 1 47 w=(1)*w 88 + (1)*w 110
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_115

theorem link1_116 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 48 w=rows1 w 116 := by
  change jetBlockRow (-1) (1) 1 48 w=(1)*w 77 + (1)*w 121
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_116

theorem link1_117 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 49 w=rows1 w 117 := by
  change jetBlockRow (-1) (1) 1 49 w=(1)*w 72 + (1)*w 78 + (1)*w 84 + (1)*w 90 + (1)*w 96 + (1)*w 102 + (1)*w 108 + (1)*w 114 + (1)*w 120 + (1)*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_117

theorem link1_118 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 50 w=rows1 w 118 := by
  change jetBlockRow (-1) (1) 1 50 w=(1)*w 75 + (1)*w 84 + (1)*w 108
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_118

theorem link1_119 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 51 w=rows1 w 119 := by
  change jetBlockRow (-1) (1) 1 51 w=(1)*w 81 + (1)*w 96 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_119

theorem link1_120 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 52 w=rows1 w 120 := by
  change jetBlockRow (-1) (1) 1 52 w=(1)*w 82 + (1)*w 98 + (1)*w 115
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_120

theorem link1_121 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 53 w=rows1 w 121 := by
  change jetBlockRow (-1) (1) 1 53 w=(1)*w 83 + (1)*w 100 + (1)*w 116
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_121

theorem link1_122 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 54 w=rows1 w 122 := by
  change jetBlockRow (-1) (1) 1 54 w=(1)*w 84 + (1)*w 102 + (1)*w 117
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_122

theorem link1_123 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 55 w=rows1 w 123 := by
  change jetBlockRow (-1) (1) 1 55 w=(1)*w 71 + (1)*w 76 + (1)*w 104
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_123

theorem link1_124 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 56 w=rows1 w 124 := by
  change jetBlockRow (-1) (1) 1 56 w=(1)*w 70 + (1)*w 74 + (1)*w 103
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_124

theorem link1_125 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 57 w=rows1 w 125 := by
  change jetBlockRow (-1) (1) 1 57 w=(1)*w 73 + (7/3)*w 87 + (1)*w 95 + (1)*w 117 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_125

theorem link1_126 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 58 w=rows1 w 126 := by
  change jetBlockRow (-1) (1) 1 58 w=(1)*w 70 + (7/3)*w 78 + (1)*w 92 + (1)*w 102 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_126

theorem link1_127 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 59 w=rows1 w 127 := by
  change jetBlockRow (-1) (1) 1 59 w=(1)*w 79 + (1)*w 92 + (1)*w 112
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_127

theorem link1_128 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 60 w=rows1 w 128 := by
  change jetBlockRow (-1) (1) 1 60 w=(1)*w 92 + (1)*w 118 + (1)*w 125
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_128

theorem link1_129 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 61 w=rows1 w 129 := by
  change jetBlockRow (-1) (1) 1 61 w=(1)*w 85 + (1)*w 104 + (1)*w 118
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_129

theorem link1_130 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 62 w=rows1 w 130 := by
  change jetBlockRow (-1) (1) 1 62 w=(1)*w 71 + (7/3)*w 81 + (1)*w 93 + (1)*w 111 + (1)*w 115
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_130

theorem link1_131 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 63 w=rows1 w 131 := by
  change jetBlockRow (-1) (1) 1 63 w=(1)*w 73 + (1)*w 80 + (1)*w 106
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_131

theorem link1_132 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 64 w=rows1 w 132 := by
  change jetBlockRow (-1) (1) 1 64 w=(1)*w 74 + (1)*w 82 + (1)*w 107
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_132

theorem link1_133 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 65 w=rows1 w 133 := by
  change jetBlockRow (-1) (1) 1 65 w=(1)*w 80 + (1)*w 94 + (1)*w 113
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_133

theorem link1_134 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 66 w=rows1 w 134 := by
  change jetBlockRow (-1) (1) 1 66 w=(1)*w 72 + (1)*w 78 + (1)*w 105
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_134

theorem link1_135 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 1 67 w=rows1 w 135 := by
  change jetBlockRow (-1) (1) 1 67 w=(1)*w 94 + (1)*w 122 + (1)*w 127
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_135

theorem link1_136 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 0 w=rows1 w 136 := by
  change jetBlockRow (-1) (1) 2 0 w=(11)*w 63 + (1)*w 129 + (1)*w 132 + (1/22)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_136

theorem link1_137 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 1 w=rows1 w 137 := by
  change jetBlockRow (-1) (1) 2 1 w=(11)*w 0 + (66)*w 66 + (198)*w 132 + (1)*w 133
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_137

theorem link1_138 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 2 w=rows1 w 138 := by
  change jetBlockRow (-1) (1) 2 2 w=(11)*w 0 + (22)*w 66 + (22)*w 132 + (1)*w 135
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_138

theorem link1_139 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 3 w=rows1 w 139 := by
  change jetBlockRow (-1) (1) 2 3 w=(11)*w 0 + ((-66))*w 66 + (198)*w 132 + (1)*w 197
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_139

theorem link1_140 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 4 w=rows1 w 140 := by
  change jetBlockRow (-1) (1) 2 4 w=((-3025))*w 65 + (55/3)*w 131 + (1)*w 162 + ((-1)/18)*w 197
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_140

theorem link1_141 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 5 w=rows1 w 141 := by
  change jetBlockRow (-1) (1) 2 5 w=((-3025))*w 0 + (110)*w 66 + ((-2))*w 132 + (1)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_141

theorem link1_142 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 6 w=rows1 w 142 := by
  change jetBlockRow (-1) (1) 2 6 w=(11)*w 64 + (2/3)*w 130 + (1)*w 165 + (2/99)*w 196
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_142

theorem link1_143 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 7 w=rows1 w 143 := by
  change jetBlockRow (-1) (1) 2 7 w=(11)*w 33 + (33)*w 99 + (1)*w 134 + (99/2)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_143

theorem link1_144 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 8 w=rows1 w 144 := by
  change jetBlockRow (-1) (1) 2 8 w=(11)*w 33 + (11)*w 99 + (1)*w 138 + (11/2)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_144

theorem link1_145 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 9 w=rows1 w 145 := by
  change jetBlockRow (-1) (1) 2 9 w=(11)*w 60 + (2)*w 126 + (1)*w 165 + (2/11)*w 192
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_145

theorem link1_146 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 10 w=rows1 w 146 := by
  change jetBlockRow (-1) (1) 2 10 w=((-3025))*w 63 + ((-165))*w 129 + (1)*w 166 + ((-9)/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_146

theorem link1_147 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 11 w=rows1 w 147 := by
  change jetBlockRow (-1) (1) 2 11 w=((-1089))*w 65 + (33)*w 131 + (1)*w 164 + ((-1)/2)*w 197
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_147

theorem link1_148 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 12 w=rows1 w 148 := by
  change jetBlockRow (-1) (1) 2 12 w=((-1089))*w 63 + ((-33))*w 129 + (1)*w 168 + ((-1)/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_148

theorem link1_149 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 13 w=rows1 w 149 := by
  change jetBlockRow (-1) (1) 2 13 w=(11)*w 44 + (22/3)*w 110 + (1)*w 141 + (22/9)*w 176
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_149

theorem link1_150 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 14 w=rows1 w 150 := by
  change jetBlockRow (-1) (1) 2 14 w=(11)*w 48 + (6)*w 114 + (1)*w 143 + (18/11)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_150

theorem link1_151 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 15 w=rows1 w 151 := by
  change jetBlockRow (-1) (1) 2 15 w=(11)*w 55 + (11/3)*w 121 + (1)*w 150 + (11/18)*w 187
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_151

theorem link1_152 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 16 w=rows1 w 152 := by
  change jetBlockRow (-1) (1) 2 16 w=(11)*w 57 + (3)*w 123 + (1)*w 154 + (9/22)*w 189
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_152

theorem link1_153 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 17 w=rows1 w 153 := by
  change jetBlockRow (-1) (1) 2 17 w=((-242))*w 4 + (22/3)*w 70 + ((-1)/9)*w 136 + (1)*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_153

theorem link1_154 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 18 w=rows1 w 154 := by
  change jetBlockRow (-1) (1) 2 18 w=((-242))*w 12 + (66)*w 78 + ((-9))*w 144 + (1)*w 194
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_154

theorem link1_155 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 19 w=rows1 w 155 := by
  change jetBlockRow (-1) (1) 2 19 w=((-1089))*w 62 + ((-66))*w 128 + (1)*w 167 + ((-2))*w 194
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_155

theorem link1_156 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 20 w=rows1 w 156 := by
  change jetBlockRow (-1) (1) 2 20 w=((-121))*w 61 + (11/3)*w 127 + (1)*w 150 + ((-1)/18)*w 193
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_156

theorem link1_157 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 21 w=rows1 w 157 := by
  change jetBlockRow (-1) (1) 2 21 w=((-121))*w 62 + (22/3)*w 128 + (1)*w 159 + ((-2)/9)*w 194
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_157

theorem link1_158 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 22 w=rows1 w 158 := by
  change jetBlockRow (-1) (1) 2 22 w=((-121))*w 42 + ((-66))*w 108 + (1)*w 169 + ((-18))*w 174
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_158

theorem link1_159 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 23 w=rows1 w 159 := by
  change jetBlockRow (-1) (1) 2 23 w=((-121))*w 51 + ((-33))*w 117 + (1)*w 170 + ((-9)/2)*w 183
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_159

theorem link1_160 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 24 w=rows1 w 160 := by
  change jetBlockRow (-1) (1) 2 24 w=((-121))*w 54 + ((-22))*w 120 + (1)*w 171 + ((-2))*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_160

theorem link1_161 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 25 w=rows1 w 161 := by
  change jetBlockRow (-1) (1) 2 25 w=((-121))*w 57 + ((-11))*w 123 + (1)*w 174 + ((-1)/2)*w 189
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_161

theorem link1_162 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 26 w=rows1 w 162 := by
  change jetBlockRow (-1) (1) 2 26 w=((-121))*w 58 + ((-22)/3)*w 124 + (1)*w 177 + ((-2)/9)*w 190
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_162

theorem link1_163 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 27 w=rows1 w 163 := by
  change jetBlockRow (-1) (1) 2 27 w=((-121))*w 59 + ((-11)/3)*w 125 + (1)*w 186 + ((-1)/18)*w 191
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_163

theorem link1_164 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 28 w=rows1 w 164 := by
  change jetBlockRow (-1) (1) 2 28 w=((-121))*w 7 + (11/3)*w 73 + ((-1)/18)*w 139 + (1)*w 144
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_164

theorem link1_165 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 29 w=rows1 w 165 := by
  change jetBlockRow (-1) (1) 2 29 w=((-121))*w 8 + (22/3)*w 74 + ((-2)/9)*w 140 + (1)*w 153
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_165

theorem link1_166 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 30 w=rows1 w 166 := by
  change jetBlockRow (-1) (1) 2 30 w=((-121))*w 9 + (11)*w 75 + ((-1)/2)*w 141 + (1)*w 156
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_166

theorem link1_167 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 31 w=rows1 w 167 := by
  change jetBlockRow (-1) (1) 2 31 w=((-121))*w 15 + (33)*w 81 + ((-9)/2)*w 147 + (1)*w 160
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_167

theorem link1_168 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 32 w=rows1 w 168 := by
  change jetBlockRow (-1) (1) 2 32 w=((-121))*w 24 + (66)*w 90 + ((-18))*w 156 + (1)*w 161
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_168

theorem link1_169 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 33 w=rows1 w 169 := by
  change jetBlockRow (-1) (1) 2 33 w=((-121))*w 54 + ((-66))*w 120 + (1)*w 163 + ((-18))*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_169

theorem link1_170 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 34 w=rows1 w 170 := by
  change jetBlockRow (-1) (1) 2 34 w=((-121))*w 5 + ((-11)/3)*w 71 + ((-1)/18)*w 137 + (1)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_170

theorem link1_171 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 35 w=rows1 w 171 := by
  change jetBlockRow (-1) (1) 2 35 w=(99)*w 11 + (99)*w 33 + (33)*w 77 + (33)*w 99 + (11/2)*w 143 + (1)*w 156 + (11/2)*w 165 + (1)*w 178
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_171

theorem link1_172 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 36 w=rows1 w 172 := by
  change jetBlockRow (-1) (1) 2 36 w=(99)*w 33 + (99)*w 55 + ((-33))*w 99 + ((-33))*w 121 + (1)*w 152 + (11/2)*w 165 + (1)*w 174 + (11/2)*w 187
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_172

theorem link1_173 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 37 w=rows1 w 173 := by
  change jetBlockRow (-1) (1) 2 37 w=((-121))*w 0 + ((-121))*w 6 + ((-121))*w 12 + ((-121))*w 18 + ((-121))*w 24 + ((-121))*w 30 + ((-121))*w 36 + ((-121))*w 42 + ((-121))*w 48 + ((-121))*w 54 + ((-22))*w 66 + ((-22))*w 72 + ((-22))*w 78 + ((-22))*w 84 + ((-22))*w 90 + ((-22))*w 96 + ((-22))*w 102 + ((-22))*w 108 + ((-22))*w 114 + ((-22))*w 120 + ((-2))*w 132 + ((-2))*w 138 + (1)*w 141 + ((-2))*w 144 + (1)*w 147 + ((-2))*w 150 + (1)*w 153 + ((-2))*w 156 + (1)*w 159 + ((-2))*w 162 + (1)*w 165 + ((-2))*w 168 + (1)*w 171 + ((-2))*w 174 + (1)*w 177 + ((-2))*w 180 + (1)*w 183 + ((-2))*w 186 + (1)*w 189 + (1)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_173

theorem link1_174 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 38 w=rows1 w 174 := by
  change jetBlockRow (-1) (1) 2 38 w=(198)*w 0 + (198)*w 22 + ((-66))*w 66 + ((-66))*w 88 + (11)*w 132 + (1)*w 142 + (11)*w 154 + (1)*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_174

theorem link1_175 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 39 w=rows1 w 175 := by
  change jetBlockRow (-1) (1) 2 39 w=(198)*w 0 + (198)*w 44 + (66)*w 66 + (66)*w 110 + (11)*w 132 + (1)*w 144 + (11)*w 176 + (1)*w 188
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_175

theorem link1_176 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 40 w=rows1 w 176 := by
  change jetBlockRow (-1) (1) 2 40 w=(99)*w 0 + (99)*w 22 + (66)*w 66 + (66)*w 88 + (22)*w 132 + (22)*w 154 + (1)*w 155 + (1)*w 177
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_176

theorem link1_177 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 41 w=rows1 w 177 := by
  change jetBlockRow (-1) (1) 2 41 w=(99)*w 0 + (99)*w 44 + ((-66))*w 66 + ((-66))*w 110 + (22)*w 132 + (1)*w 153 + (1)*w 175 + (22)*w 176
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_177

theorem link1_178 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 42 w=rows1 w 178 := by
  change jetBlockRow (-1) (1) 2 42 w=((-121))*w 0 + ((-121))*w 6 + ((-121))*w 12 + ((-121))*w 18 + ((-121))*w 24 + ((-121))*w 30 + ((-121))*w 36 + ((-121))*w 42 + ((-121))*w 54 + ((-121))*w 60 + ((-66))*w 66 + ((-66))*w 72 + ((-66))*w 78 + ((-66))*w 84 + ((-66))*w 90 + ((-66))*w 96 + ((-66))*w 102 + ((-66))*w 108 + ((-66))*w 120 + ((-66))*w 126 + ((-18))*w 132 + ((-18))*w 138 + (1)*w 139 + ((-18))*w 144 + (1)*w 145 + ((-18))*w 150 + (1)*w 151 + ((-18))*w 156 + (1)*w 157 + ((-18))*w 162 + (1)*w 163 + ((-18))*w 168 + (1)*w 169 + ((-18))*w 174 + (1)*w 175 + (1)*w 181 + ((-18))*w 186 + (1)*w 187 + ((-18))*w 192 + (1)*w 193
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_178

theorem link1_179 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 43 w=rows1 w 179 := by
  change jetBlockRow (-1) (1) 2 43 w=((-121))*w 3 + ((-121))*w 15 + ((-121))*w 21 + ((-121))*w 27 + ((-121))*w 33 + ((-121))*w 39 + ((-121))*w 45 + ((-121))*w 51 + ((-121))*w 57 + ((-121))*w 63 + (33)*w 69 + (33)*w 81 + (33)*w 87 + (33)*w 93 + (33)*w 99 + (33)*w 105 + (33)*w 111 + (33)*w 117 + (33)*w 123 + (33)*w 129 + ((-9)/2)*w 135 + (1)*w 136 + (1)*w 142 + ((-9)/2)*w 147 + (1)*w 148 + ((-9)/2)*w 153 + (1)*w 154 + ((-9)/2)*w 159 + (1)*w 160 + ((-9)/2)*w 165 + (1)*w 166 + ((-9)/2)*w 171 + (1)*w 172 + ((-9)/2)*w 177 + (1)*w 178 + ((-9)/2)*w 183 + (1)*w 184 + ((-9)/2)*w 189 + (1)*w 190 + ((-9)/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_179

theorem link1_180 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 44 w=rows1 w 180 := by
  change jetBlockRow (-1) (1) 2 44 w=((-121))*w 3 + ((-121))*w 9 + ((-121))*w 15 + ((-121))*w 21 + ((-121))*w 27 + ((-121))*w 33 + ((-121))*w 39 + ((-121))*w 45 + ((-121))*w 51 + ((-121))*w 63 + ((-33))*w 69 + ((-33))*w 75 + ((-33))*w 81 + ((-33))*w 87 + ((-33))*w 93 + ((-33))*w 99 + ((-33))*w 105 + ((-33))*w 111 + ((-33))*w 117 + ((-33))*w 129 + ((-9)/2)*w 135 + (1)*w 140 + ((-9)/2)*w 141 + (1)*w 146 + ((-9)/2)*w 147 + (1)*w 152 + ((-9)/2)*w 153 + (1)*w 158 + ((-9)/2)*w 159 + (1)*w 164 + ((-9)/2)*w 165 + (1)*w 170 + ((-9)/2)*w 171 + (1)*w 176 + ((-9)/2)*w 177 + (1)*w 182 + ((-9)/2)*w 183 + (1)*w 188 + (1)*w 194 + ((-9)/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_180

theorem link1_181 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 45 w=rows1 w 181 := by
  change jetBlockRow (-1) (1) 2 45 w=((-121))*w 0 + ((-121))*w 6 + ((-121))*w 12 + ((-121))*w 24 + ((-121))*w 30 + ((-121))*w 36 + ((-121))*w 42 + ((-121))*w 48 + ((-121))*w 54 + ((-121))*w 60 + (66)*w 66 + (66)*w 72 + (66)*w 78 + (66)*w 90 + (66)*w 96 + (66)*w 102 + (66)*w 108 + (66)*w 114 + (66)*w 120 + (66)*w 126 + ((-18))*w 132 + (1)*w 137 + ((-18))*w 138 + (1)*w 143 + ((-18))*w 144 + (1)*w 149 + (1)*w 155 + ((-18))*w 156 + (1)*w 161 + ((-18))*w 162 + (1)*w 167 + ((-18))*w 168 + (1)*w 173 + ((-18))*w 174 + (1)*w 179 + ((-18))*w 180 + (1)*w 185 + ((-18))*w 186 + (1)*w 191 + ((-18))*w 192
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_181

theorem link1_182 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 46 w=rows1 w 182 := by
  change jetBlockRow (-1) (1) 2 46 w=(1)*w 132
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_182

theorem link1_183 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 47 w=rows1 w 183 := by
  change jetBlockRow (-1) (1) 2 47 w=(1)*w 154 + (1)*w 176
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_183

theorem link1_184 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 48 w=rows1 w 184 := by
  change jetBlockRow (-1) (1) 2 48 w=(1)*w 143 + (1)*w 187
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_184

theorem link1_185 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 49 w=rows1 w 185 := by
  change jetBlockRow (-1) (1) 2 49 w=(1)*w 138 + (1)*w 144 + (1)*w 150 + (1)*w 156 + (1)*w 162 + (1)*w 168 + (1)*w 174 + (1)*w 180 + (1)*w 186 + (1)*w 192
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_185

theorem link1_186 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 50 w=rows1 w 186 := by
  change jetBlockRow (-1) (1) 2 50 w=(1)*w 141 + (2)*w 150 + (1)*w 174
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_186

theorem link1_187 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 51 w=rows1 w 187 := by
  change jetBlockRow (-1) (1) 2 51 w=(1)*w 147 + (2)*w 162 + (1)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_187

theorem link1_188 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 52 w=rows1 w 188 := by
  change jetBlockRow (-1) (1) 2 52 w=(1)*w 148 + (2)*w 164 + (1)*w 181
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_188

theorem link1_189 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 53 w=rows1 w 189 := by
  change jetBlockRow (-1) (1) 2 53 w=(1)*w 149 + (2)*w 166 + (1)*w 182
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_189

theorem link1_190 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 54 w=rows1 w 190 := by
  change jetBlockRow (-1) (1) 2 54 w=(1)*w 150 + (2)*w 168 + (1)*w 183
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_190

theorem link1_191 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 55 w=rows1 w 191 := by
  change jetBlockRow (-1) (1) 2 55 w=(1)*w 137 + (2)*w 142 + (1)*w 170
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_191

theorem link1_192 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 56 w=rows1 w 192 := by
  change jetBlockRow (-1) (1) 2 56 w=(1)*w 136 + (2)*w 140 + (1)*w 169
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_192

theorem link1_193 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 57 w=rows1 w 193 := by
  change jetBlockRow (-1) (1) 2 57 w=(1)*w 139 + (7)*w 153 + (1)*w 161 + (1)*w 183 + (9)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_193

theorem link1_194 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 58 w=rows1 w 194 := by
  change jetBlockRow (-1) (1) 2 58 w=(1)*w 136 + (7)*w 144 + (1)*w 158 + (9)*w 168 + (1)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_194

theorem link1_195 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 59 w=rows1 w 195 := by
  change jetBlockRow (-1) (1) 2 59 w=(1)*w 145 + (2)*w 158 + (1)*w 178
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_195

theorem link1_196 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 60 w=rows1 w 196 := by
  change jetBlockRow (-1) (1) 2 60 w=(1)*w 158 + (2)*w 184 + (1)*w 191
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_196

theorem link1_197 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 61 w=rows1 w 197 := by
  change jetBlockRow (-1) (1) 2 61 w=(1)*w 151 + (2)*w 170 + (1)*w 184
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_197

theorem link1_198 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 62 w=rows1 w 198 := by
  change jetBlockRow (-1) (1) 2 62 w=(1)*w 137 + (7)*w 147 + (1)*w 159 + (9)*w 177 + (1)*w 181
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_198

theorem link1_199 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 63 w=rows1 w 199 := by
  change jetBlockRow (-1) (1) 2 63 w=(1)*w 139 + (2)*w 146 + (1)*w 172
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_199

theorem link1_200 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 64 w=rows1 w 200 := by
  change jetBlockRow (-1) (1) 2 64 w=(1)*w 140 + (2)*w 148 + (1)*w 173
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_200

theorem link1_201 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 65 w=rows1 w 201 := by
  change jetBlockRow (-1) (1) 2 65 w=(1)*w 146 + (2)*w 160 + (1)*w 179
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_201

theorem link1_202 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 66 w=rows1 w 202 := by
  change jetBlockRow (-1) (1) 2 66 w=(1)*w 138 + (2)*w 144 + (1)*w 171
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_202

theorem link1_203 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 2 67 w=rows1 w 203 := by
  change jetBlockRow (-1) (1) 2 67 w=(1)*w 160 + (2)*w 188 + (1)*w 193
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_203

theorem link1_204 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 0 w=rows1 w 204 := by
  change jetBlockRow (-1) (1) 3 0 w=(11/3)*w 63 + (1/2)*w 129 + (1/22)*w 195 + (1)*w 198 + (1/484)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_204

theorem link1_205 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 1 w=rows1 w 205 := by
  change jetBlockRow (-1) (1) 3 1 w=(242)*w 0 + (2178)*w 66 + (13068)*w 132 + (39204)*w 198 + (1)*w 199
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_205

theorem link1_206 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 2 w=rows1 w 206 := by
  change jetBlockRow (-1) (1) 3 2 w=(242/3)*w 0 + (242)*w 66 + (484)*w 132 + (484)*w 198 + (1)*w 201
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_206

theorem link1_207 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 3 w=rows1 w 207 := by
  change jetBlockRow (-1) (1) 3 3 w=((-242))*w 0 + (2178)*w 66 + ((-13068))*w 132 + (39204)*w 198 + (1)*w 263
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_207

theorem link1_208 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 4 w=rows1 w 208 := by
  change jetBlockRow (-1) (1) 3 4 w=(166375/9)*w 65 + ((-3025)/18)*w 131 + (55/54)*w 197 + (1)*w 228 + ((-1)/324)*w 263
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_208

theorem link1_209 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 5 w=rows1 w 209 := by
  change jetBlockRow (-1) (1) 3 5 w=(332750/3)*w 0 + ((-6050))*w 66 + (220)*w 132 + ((-4))*w 198 + (1)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_209

theorem link1_210 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 6 w=rows1 w 210 := by
  change jetBlockRow (-1) (1) 3 6 w=(22/9)*w 64 + (2/9)*w 130 + (4/297)*w 196 + (1)*w 231 + (4/9801)*w 262
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_210

theorem link1_211 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 7 w=rows1 w 211 := by
  change jetBlockRow (-1) (1) 3 7 w=(121)*w 33 + (1089/2)*w 99 + (3267/2)*w 165 + (1)*w 200 + (9801/4)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_211

theorem link1_212 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 8 w=rows1 w 212 := by
  change jetBlockRow (-1) (1) 3 8 w=(121/3)*w 33 + (121/2)*w 99 + (121/2)*w 165 + (1)*w 204 + (121/4)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_212

theorem link1_213 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 9 w=rows1 w 213 := by
  change jetBlockRow (-1) (1) 3 9 w=(22/3)*w 60 + (2)*w 126 + (4/11)*w 192 + (1)*w 231 + (4/121)*w 258
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_213

theorem link1_214 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 10 w=rows1 w 214 := by
  change jetBlockRow (-1) (1) 3 10 w=((-166375))*w 63 + ((-27225)/2)*w 129 + ((-1485)/2)*w 195 + (1)*w 232 + ((-81)/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_214

theorem link1_215 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 11 w=rows1 w 215 := by
  change jetBlockRow (-1) (1) 3 11 w=(11979)*w 65 + ((-1089)/2)*w 131 + (33/2)*w 197 + (1)*w 230 + ((-1)/4)*w 263
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_215

theorem link1_216 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 12 w=rows1 w 216 := by
  change jetBlockRow (-1) (1) 3 12 w=((-11979))*w 63 + ((-1089)/2)*w 129 + ((-33)/2)*w 195 + (1)*w 234 + ((-1)/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_216

theorem link1_217 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 13 w=rows1 w 217 := by
  change jetBlockRow (-1) (1) 3 13 w=(242/9)*w 44 + (242/9)*w 110 + (484/27)*w 176 + (1)*w 207 + (484/81)*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_217

theorem link1_218 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 14 w=rows1 w 218 := by
  change jetBlockRow (-1) (1) 3 14 w=(22)*w 48 + (18)*w 114 + (108/11)*w 180 + (1)*w 209 + (324/121)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_218

theorem link1_219 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 15 w=rows1 w 219 := by
  change jetBlockRow (-1) (1) 3 15 w=(121/9)*w 55 + (121/18)*w 121 + (121/54)*w 187 + (1)*w 216 + (121/324)*w 253
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_219

theorem link1_220 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 16 w=rows1 w 220 := by
  change jetBlockRow (-1) (1) 3 16 w=(11)*w 57 + (9/2)*w 123 + (27/22)*w 189 + (1)*w 220 + (81/484)*w 255
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_220

theorem link1_221 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 17 w=rows1 w 221 := by
  change jetBlockRow (-1) (1) 3 17 w=(5324/9)*w 4 + ((-242)/9)*w 70 + (22/27)*w 136 + ((-1)/81)*w 202 + (1)*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_221

theorem link1_222 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 18 w=rows1 w 222 := by
  change jetBlockRow (-1) (1) 3 18 w=(5324)*w 12 + ((-2178))*w 78 + (594)*w 144 + ((-81))*w 210 + (1)*w 260
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_222

theorem link1_223 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 19 w=rows1 w 223 := by
  change jetBlockRow (-1) (1) 3 19 w=((-23958))*w 62 + ((-2178))*w 128 + ((-132))*w 194 + (1)*w 233 + ((-4))*w 260
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_223

theorem link1_224 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 20 w=rows1 w 224 := by
  change jetBlockRow (-1) (1) 3 20 w=(1331/9)*w 61 + ((-121)/18)*w 127 + (11/54)*w 193 + (1)*w 216 + ((-1)/324)*w 259
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_224

theorem link1_225 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 21 w=rows1 w 225 := by
  change jetBlockRow (-1) (1) 3 21 w=(2662/9)*w 62 + ((-242)/9)*w 128 + (44/27)*w 194 + (1)*w 225 + ((-4)/81)*w 260
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_225

theorem link1_226 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 22 w=rows1 w 226 := by
  change jetBlockRow (-1) (1) 3 22 w=((-2662))*w 42 + ((-2178))*w 108 + ((-1188))*w 174 + (1)*w 235 + ((-324))*w 240
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_226

theorem link1_227 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 23 w=rows1 w 227 := by
  change jetBlockRow (-1) (1) 3 23 w=((-1331))*w 51 + ((-1089)/2)*w 117 + ((-297)/2)*w 183 + (1)*w 236 + ((-81)/4)*w 249
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_227

theorem link1_228 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 24 w=rows1 w 228 := by
  change jetBlockRow (-1) (1) 3 24 w=((-2662)/3)*w 54 + ((-242))*w 120 + ((-44))*w 186 + (1)*w 237 + ((-4))*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_228

theorem link1_229 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 25 w=rows1 w 229 := by
  change jetBlockRow (-1) (1) 3 25 w=((-1331)/3)*w 57 + ((-121)/2)*w 123 + ((-11)/2)*w 189 + (1)*w 240 + ((-1)/4)*w 255
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_229

theorem link1_230 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 26 w=rows1 w 230 := by
  change jetBlockRow (-1) (1) 3 26 w=((-2662)/9)*w 58 + ((-242)/9)*w 124 + ((-44)/27)*w 190 + (1)*w 243 + ((-4)/81)*w 256
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_230

theorem link1_231 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 27 w=rows1 w 231 := by
  change jetBlockRow (-1) (1) 3 27 w=((-1331)/9)*w 59 + ((-121)/18)*w 125 + ((-11)/54)*w 191 + (1)*w 252 + ((-1)/324)*w 257
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_231

theorem link1_232 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 28 w=rows1 w 232 := by
  change jetBlockRow (-1) (1) 3 28 w=(1331/9)*w 7 + ((-121)/18)*w 73 + (11/54)*w 139 + ((-1)/324)*w 205 + (1)*w 210
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_232

theorem link1_233 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 29 w=rows1 w 233 := by
  change jetBlockRow (-1) (1) 3 29 w=(2662/9)*w 8 + ((-242)/9)*w 74 + (44/27)*w 140 + ((-4)/81)*w 206 + (1)*w 219
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_233

theorem link1_234 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 30 w=rows1 w 234 := by
  change jetBlockRow (-1) (1) 3 30 w=(1331/3)*w 9 + ((-121)/2)*w 75 + (11/2)*w 141 + ((-1)/4)*w 207 + (1)*w 222
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_234

theorem link1_235 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 31 w=rows1 w 235 := by
  change jetBlockRow (-1) (1) 3 31 w=(1331)*w 15 + ((-1089)/2)*w 81 + (297/2)*w 147 + ((-81)/4)*w 213 + (1)*w 226
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_235

theorem link1_236 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 32 w=rows1 w 236 := by
  change jetBlockRow (-1) (1) 3 32 w=(2662)*w 24 + ((-2178))*w 90 + (1188)*w 156 + ((-324))*w 222 + (1)*w 227
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_236

theorem link1_237 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 33 w=rows1 w 237 := by
  change jetBlockRow (-1) (1) 3 33 w=((-2662))*w 54 + ((-2178))*w 120 + ((-1188))*w 186 + (1)*w 229 + ((-324))*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_237

theorem link1_238 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 34 w=rows1 w 238 := by
  change jetBlockRow (-1) (1) 3 34 w=((-1331)/9)*w 5 + ((-121)/18)*w 71 + ((-11)/54)*w 137 + ((-1)/324)*w 203 + (1)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_238

theorem link1_239 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 35 w=rows1 w 239 := by
  change jetBlockRow (-1) (1) 3 35 w=(1089)*w 11 + (1089)*w 33 + (1089/2)*w 77 + (1089/2)*w 99 + (363/2)*w 143 + (363/2)*w 165 + (121/4)*w 209 + (1)*w 222 + (121/4)*w 231 + (1)*w 244
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_239

theorem link1_240 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 36 w=rows1 w 240 := by
  change jetBlockRow (-1) (1) 3 36 w=((-1089))*w 33 + ((-1089))*w 55 + (1089/2)*w 99 + (1089/2)*w 121 + ((-363)/2)*w 165 + ((-363)/2)*w 187 + (1)*w 218 + (121/4)*w 231 + (1)*w 240 + (121/4)*w 253
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_240

theorem link1_241 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 37 w=rows1 w 241 := by
  change jetBlockRow (-1) (1) 3 37 w=((-2662)/3)*w 0 + ((-2662)/3)*w 6 + ((-2662)/3)*w 12 + ((-2662)/3)*w 18 + ((-2662)/3)*w 24 + ((-2662)/3)*w 30 + ((-2662)/3)*w 36 + ((-2662)/3)*w 42 + ((-2662)/3)*w 48 + ((-2662)/3)*w 54 + ((-242))*w 66 + ((-242))*w 72 + ((-242))*w 78 + ((-242))*w 84 + ((-242))*w 90 + ((-242))*w 96 + ((-242))*w 102 + ((-242))*w 108 + ((-242))*w 114 + ((-242))*w 120 + ((-44))*w 132 + ((-44))*w 138 + ((-44))*w 144 + ((-44))*w 150 + ((-44))*w 156 + ((-44))*w 162 + ((-44))*w 168 + ((-44))*w 174 + ((-44))*w 180 + ((-44))*w 186 + ((-4))*w 198 + ((-4))*w 204 + (1)*w 207 + ((-4))*w 210 + (1)*w 213 + ((-4))*w 216 + (1)*w 219 + ((-4))*w 222 + (1)*w 225 + ((-4))*w 228 + (1)*w 231 + ((-4))*w 234 + (1)*w 237 + ((-4))*w 240 + (1)*w 243 + ((-4))*w 246 + (1)*w 249 + ((-4))*w 252 + (1)*w 255 + (1)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_241

theorem link1_242 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 38 w=rows1 w 242 := by
  change jetBlockRow (-1) (1) 3 38 w=((-4356))*w 0 + ((-4356))*w 22 + (2178)*w 66 + (2178)*w 88 + ((-726))*w 132 + ((-726))*w 154 + (121)*w 198 + (1)*w 208 + (121)*w 220 + (1)*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_242

theorem link1_243 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 39 w=rows1 w 243 := by
  change jetBlockRow (-1) (1) 3 39 w=(4356)*w 0 + (4356)*w 44 + (2178)*w 66 + (2178)*w 110 + (726)*w 132 + (726)*w 176 + (121)*w 198 + (1)*w 210 + (121)*w 242 + (1)*w 254
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_243

theorem link1_244 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 40 w=rows1 w 244 := by
  change jetBlockRow (-1) (1) 3 40 w=(2178)*w 0 + (2178)*w 22 + (2178)*w 66 + (2178)*w 88 + (1452)*w 132 + (1452)*w 154 + (484)*w 198 + (484)*w 220 + (1)*w 221 + (1)*w 243
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_244

theorem link1_245 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 41 w=rows1 w 245 := by
  change jetBlockRow (-1) (1) 3 41 w=((-2178))*w 0 + ((-2178))*w 44 + (2178)*w 66 + (2178)*w 110 + ((-1452))*w 132 + ((-1452))*w 176 + (484)*w 198 + (1)*w 219 + (1)*w 241 + (484)*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_245

theorem link1_246 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 42 w=rows1 w 246 := by
  change jetBlockRow (-1) (1) 3 42 w=((-2662))*w 0 + ((-2662))*w 6 + ((-2662))*w 12 + ((-2662))*w 18 + ((-2662))*w 24 + ((-2662))*w 30 + ((-2662))*w 36 + ((-2662))*w 42 + ((-2662))*w 54 + ((-2662))*w 60 + ((-2178))*w 66 + ((-2178))*w 72 + ((-2178))*w 78 + ((-2178))*w 84 + ((-2178))*w 90 + ((-2178))*w 96 + ((-2178))*w 102 + ((-2178))*w 108 + ((-2178))*w 120 + ((-2178))*w 126 + ((-1188))*w 132 + ((-1188))*w 138 + ((-1188))*w 144 + ((-1188))*w 150 + ((-1188))*w 156 + ((-1188))*w 162 + ((-1188))*w 168 + ((-1188))*w 174 + ((-1188))*w 186 + ((-1188))*w 192 + ((-324))*w 198 + ((-324))*w 204 + (1)*w 205 + ((-324))*w 210 + (1)*w 211 + ((-324))*w 216 + (1)*w 217 + ((-324))*w 222 + (1)*w 223 + ((-324))*w 228 + (1)*w 229 + ((-324))*w 234 + (1)*w 235 + ((-324))*w 240 + (1)*w 241 + (1)*w 247 + ((-324))*w 252 + (1)*w 253 + ((-324))*w 258 + (1)*w 259
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_246

theorem link1_247 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 43 w=rows1 w 247 := by
  change jetBlockRow (-1) (1) 3 43 w=(1331)*w 3 + (1331)*w 15 + (1331)*w 21 + (1331)*w 27 + (1331)*w 33 + (1331)*w 39 + (1331)*w 45 + (1331)*w 51 + (1331)*w 57 + (1331)*w 63 + ((-1089)/2)*w 69 + ((-1089)/2)*w 81 + ((-1089)/2)*w 87 + ((-1089)/2)*w 93 + ((-1089)/2)*w 99 + ((-1089)/2)*w 105 + ((-1089)/2)*w 111 + ((-1089)/2)*w 117 + ((-1089)/2)*w 123 + ((-1089)/2)*w 129 + (297/2)*w 135 + (297/2)*w 147 + (297/2)*w 153 + (297/2)*w 159 + (297/2)*w 165 + (297/2)*w 171 + (297/2)*w 177 + (297/2)*w 183 + (297/2)*w 189 + (297/2)*w 195 + ((-81)/4)*w 201 + (1)*w 202 + (1)*w 208 + ((-81)/4)*w 213 + (1)*w 214 + ((-81)/4)*w 219 + (1)*w 220 + ((-81)/4)*w 225 + (1)*w 226 + ((-81)/4)*w 231 + (1)*w 232 + ((-81)/4)*w 237 + (1)*w 238 + ((-81)/4)*w 243 + (1)*w 244 + ((-81)/4)*w 249 + (1)*w 250 + ((-81)/4)*w 255 + (1)*w 256 + ((-81)/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_247

theorem link1_248 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 44 w=rows1 w 248 := by
  change jetBlockRow (-1) (1) 3 44 w=((-1331))*w 3 + ((-1331))*w 9 + ((-1331))*w 15 + ((-1331))*w 21 + ((-1331))*w 27 + ((-1331))*w 33 + ((-1331))*w 39 + ((-1331))*w 45 + ((-1331))*w 51 + ((-1331))*w 63 + ((-1089)/2)*w 69 + ((-1089)/2)*w 75 + ((-1089)/2)*w 81 + ((-1089)/2)*w 87 + ((-1089)/2)*w 93 + ((-1089)/2)*w 99 + ((-1089)/2)*w 105 + ((-1089)/2)*w 111 + ((-1089)/2)*w 117 + ((-1089)/2)*w 129 + ((-297)/2)*w 135 + ((-297)/2)*w 141 + ((-297)/2)*w 147 + ((-297)/2)*w 153 + ((-297)/2)*w 159 + ((-297)/2)*w 165 + ((-297)/2)*w 171 + ((-297)/2)*w 177 + ((-297)/2)*w 183 + ((-297)/2)*w 195 + ((-81)/4)*w 201 + (1)*w 206 + ((-81)/4)*w 207 + (1)*w 212 + ((-81)/4)*w 213 + (1)*w 218 + ((-81)/4)*w 219 + (1)*w 224 + ((-81)/4)*w 225 + (1)*w 230 + ((-81)/4)*w 231 + (1)*w 236 + ((-81)/4)*w 237 + (1)*w 242 + ((-81)/4)*w 243 + (1)*w 248 + ((-81)/4)*w 249 + (1)*w 254 + (1)*w 260 + ((-81)/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_248

theorem link1_249 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 45 w=rows1 w 249 := by
  change jetBlockRow (-1) (1) 3 45 w=(2662)*w 0 + (2662)*w 6 + (2662)*w 12 + (2662)*w 24 + (2662)*w 30 + (2662)*w 36 + (2662)*w 42 + (2662)*w 48 + (2662)*w 54 + (2662)*w 60 + ((-2178))*w 66 + ((-2178))*w 72 + ((-2178))*w 78 + ((-2178))*w 90 + ((-2178))*w 96 + ((-2178))*w 102 + ((-2178))*w 108 + ((-2178))*w 114 + ((-2178))*w 120 + ((-2178))*w 126 + (1188)*w 132 + (1188)*w 138 + (1188)*w 144 + (1188)*w 156 + (1188)*w 162 + (1188)*w 168 + (1188)*w 174 + (1188)*w 180 + (1188)*w 186 + (1188)*w 192 + ((-324))*w 198 + (1)*w 203 + ((-324))*w 204 + (1)*w 209 + ((-324))*w 210 + (1)*w 215 + (1)*w 221 + ((-324))*w 222 + (1)*w 227 + ((-324))*w 228 + (1)*w 233 + ((-324))*w 234 + (1)*w 239 + ((-324))*w 240 + (1)*w 245 + ((-324))*w 246 + (1)*w 251 + ((-324))*w 252 + (1)*w 257 + ((-324))*w 258
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_249

theorem link1_250 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 46 w=rows1 w 250 := by
  change jetBlockRow (-1) (1) 3 46 w=(1)*w 198
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_250

theorem link1_251 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 47 w=rows1 w 251 := by
  change jetBlockRow (-1) (1) 3 47 w=(1)*w 220 + (1)*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_251

theorem link1_252 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 48 w=rows1 w 252 := by
  change jetBlockRow (-1) (1) 3 48 w=(1)*w 209 + (1)*w 253
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_252

theorem link1_253 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 49 w=rows1 w 253 := by
  change jetBlockRow (-1) (1) 3 49 w=(1)*w 204 + (1)*w 210 + (1)*w 216 + (1)*w 222 + (1)*w 228 + (1)*w 234 + (1)*w 240 + (1)*w 246 + (1)*w 252 + (1)*w 258
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_253

theorem link1_254 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 50 w=rows1 w 254 := by
  change jetBlockRow (-1) (1) 3 50 w=(1)*w 207 + (4)*w 216 + (1)*w 240
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_254

theorem link1_255 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 51 w=rows1 w 255 := by
  change jetBlockRow (-1) (1) 3 51 w=(1)*w 213 + (4)*w 228 + (1)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_255

theorem link1_256 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 52 w=rows1 w 256 := by
  change jetBlockRow (-1) (1) 3 52 w=(1)*w 214 + (4)*w 230 + (1)*w 247
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_256

theorem link1_257 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 53 w=rows1 w 257 := by
  change jetBlockRow (-1) (1) 3 53 w=(1)*w 215 + (4)*w 232 + (1)*w 248
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_257

theorem link1_258 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 54 w=rows1 w 258 := by
  change jetBlockRow (-1) (1) 3 54 w=(1)*w 216 + (4)*w 234 + (1)*w 249
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_258

theorem link1_259 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 55 w=rows1 w 259 := by
  change jetBlockRow (-1) (1) 3 55 w=(1)*w 203 + (4)*w 208 + (1)*w 236
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_259

theorem link1_260 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 56 w=rows1 w 260 := by
  change jetBlockRow (-1) (1) 3 56 w=(1)*w 202 + (4)*w 206 + (1)*w 235
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_260

theorem link1_261 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 57 w=rows1 w 261 := by
  change jetBlockRow (-1) (1) 3 57 w=(1)*w 205 + (21)*w 219 + (1)*w 227 + (1)*w 249 + (81)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_261

theorem link1_262 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 58 w=rows1 w 262 := by
  change jetBlockRow (-1) (1) 3 58 w=(1)*w 202 + (21)*w 210 + (1)*w 224 + (81)*w 234 + (1)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_262

theorem link1_263 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 59 w=rows1 w 263 := by
  change jetBlockRow (-1) (1) 3 59 w=(1)*w 211 + (4)*w 224 + (1)*w 244
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_263

theorem link1_264 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 60 w=rows1 w 264 := by
  change jetBlockRow (-1) (1) 3 60 w=(1)*w 224 + (4)*w 250 + (1)*w 257
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_264

theorem link1_265 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 61 w=rows1 w 265 := by
  change jetBlockRow (-1) (1) 3 61 w=(1)*w 217 + (4)*w 236 + (1)*w 250
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_265

theorem link1_266 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 62 w=rows1 w 266 := by
  change jetBlockRow (-1) (1) 3 62 w=(1)*w 203 + (21)*w 213 + (1)*w 225 + (81)*w 243 + (1)*w 247
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_266

theorem link1_267 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 63 w=rows1 w 267 := by
  change jetBlockRow (-1) (1) 3 63 w=(1)*w 205 + (4)*w 212 + (1)*w 238
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_267

theorem link1_268 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 64 w=rows1 w 268 := by
  change jetBlockRow (-1) (1) 3 64 w=(1)*w 206 + (4)*w 214 + (1)*w 239
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_268

theorem link1_269 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 65 w=rows1 w 269 := by
  change jetBlockRow (-1) (1) 3 65 w=(1)*w 212 + (4)*w 226 + (1)*w 245
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_269

theorem link1_270 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 66 w=rows1 w 270 := by
  change jetBlockRow (-1) (1) 3 66 w=(1)*w 204 + (4)*w 210 + (1)*w 237
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_270

theorem link1_271 (w : Fin 264→ℂ) : jetBlockRow (-1) (1) 3 67 w=rows1 w 271 := by
  change jetBlockRow (-1) (1) 3 67 w=(1)*w 226 + (4)*w 254 + (1)*w 259
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link1_271

end SmallLevelTwentyTwoJetBlock
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoJetBlock
open Complex SmallLevelFiniteShift SmallLevelTwentyTwoLaurent SmallLevelTwentyTwoThirdJet

theorem link2_0 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 0 w=rows2 w 0 := by
  change jetBlockRow (1) (-1) 0 0 w=(1)*w 0 + ((-22))*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_0

theorem link2_1 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 1 w=rows2 w 1 := by
  change jetBlockRow (1) (-1) 0 1 w=((-1)/198)*w 0 + (1)*w 1
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_1

theorem link2_2 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 2 w=rows2 w 2 := by
  change jetBlockRow (1) (-1) 0 2 w=((-1)/22)*w 0 + (1)*w 3
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_2

theorem link2_3 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 3 w=rows2 w 3 := by
  change jetBlockRow (1) (-1) 0 3 w=((-1)/198)*w 0 + (1)*w 65
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_3

theorem link2_4 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 4 w=rows2 w 4 := by
  change jetBlockRow (1) (-1) 0 4 w=(1)*w 30 + ((-18))*w 65
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_4

theorem link2_5 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 5 w=rows2 w 5 := by
  change jetBlockRow (1) (-1) 0 5 w=((-1)/2)*w 0 + (1)*w 33
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_5

theorem link2_6 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 6 w=rows2 w 6 := by
  change jetBlockRow (1) (-1) 0 6 w=(1)*w 33 + ((-99)/2)*w 64
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_6

theorem link2_7 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 7 w=rows2 w 7 := by
  change jetBlockRow (1) (-1) 0 7 w=(1)*w 2 + ((-2)/99)*w 33
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_7

theorem link2_8 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 8 w=rows2 w 8 := by
  change jetBlockRow (1) (-1) 0 8 w=(1)*w 6 + ((-2)/11)*w 33
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_8

theorem link2_9 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 9 w=rows2 w 9 := by
  change jetBlockRow (1) (-1) 0 9 w=(1)*w 33 + ((-11)/2)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_9

theorem link2_10 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 10 w=rows2 w 10 := by
  change jetBlockRow (1) (-1) 0 10 w=(1)*w 34 + ((-2)/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_10

theorem link2_11 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 11 w=rows2 w 11 := by
  change jetBlockRow (1) (-1) 0 11 w=(1)*w 32 + ((-2))*w 65
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_11

theorem link2_12 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 12 w=rows2 w 12 := by
  change jetBlockRow (1) (-1) 0 12 w=(1)*w 36 + ((-2))*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_12

theorem link2_13 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 13 w=rows2 w 13 := by
  change jetBlockRow (1) (-1) 0 13 w=(1)*w 9 + ((-9)/22)*w 44
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_13

theorem link2_14 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 14 w=rows2 w 14 := by
  change jetBlockRow (1) (-1) 0 14 w=(1)*w 11 + ((-11)/18)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_14

theorem link2_15 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 15 w=rows2 w 15 := by
  change jetBlockRow (1) (-1) 0 15 w=(1)*w 18 + ((-18)/11)*w 55
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_15

theorem link2_16 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 16 w=rows2 w 16 := by
  change jetBlockRow (1) (-1) 0 16 w=(1)*w 22 + ((-22)/9)*w 57
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_16

theorem link2_17 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 17 w=rows2 w 17 := by
  change jetBlockRow (1) (-1) 0 17 w=((-9))*w 4 + (1)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_17

theorem link2_18 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 18 w=rows2 w 18 := by
  change jetBlockRow (1) (-1) 0 18 w=((-1)/9)*w 12 + (1)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_18

theorem link2_19 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 19 w=rows2 w 19 := by
  change jetBlockRow (1) (-1) 0 19 w=(1)*w 35 + ((-1)/2)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_19

theorem link2_20 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 20 w=rows2 w 20 := by
  change jetBlockRow (1) (-1) 0 20 w=(1)*w 18 + ((-18))*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_20

theorem link2_21 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 21 w=rows2 w 21 := by
  change jetBlockRow (1) (-1) 0 21 w=(1)*w 27 + ((-9)/2)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_21

theorem link2_22 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 22 w=rows2 w 22 := by
  change jetBlockRow (1) (-1) 0 22 w=(1)*w 37 + ((-1)/18)*w 42
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_22

theorem link2_23 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 23 w=rows2 w 23 := by
  change jetBlockRow (1) (-1) 0 23 w=(1)*w 38 + ((-2)/9)*w 51
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_23

theorem link2_24 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 24 w=rows2 w 24 := by
  change jetBlockRow (1) (-1) 0 24 w=(1)*w 39 + ((-1)/2)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_24

theorem link2_25 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 25 w=rows2 w 25 := by
  change jetBlockRow (1) (-1) 0 25 w=(1)*w 42 + ((-2))*w 57
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_25

theorem link2_26 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 26 w=rows2 w 26 := by
  change jetBlockRow (1) (-1) 0 26 w=(1)*w 45 + ((-9)/2)*w 58
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_26

theorem link2_27 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 27 w=rows2 w 27 := by
  change jetBlockRow (1) (-1) 0 27 w=(1)*w 54 + ((-18))*w 59
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_27

theorem link2_28 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 28 w=rows2 w 28 := by
  change jetBlockRow (1) (-1) 0 28 w=((-18))*w 7 + (1)*w 12
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_28

theorem link2_29 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 29 w=rows2 w 29 := by
  change jetBlockRow (1) (-1) 0 29 w=((-9)/2)*w 8 + (1)*w 21
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_29

theorem link2_30 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 30 w=rows2 w 30 := by
  change jetBlockRow (1) (-1) 0 30 w=((-2))*w 9 + (1)*w 24
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_30

theorem link2_31 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 31 w=rows2 w 31 := by
  change jetBlockRow (1) (-1) 0 31 w=((-2)/9)*w 15 + (1)*w 28
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_31

theorem link2_32 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 32 w=rows2 w 32 := by
  change jetBlockRow (1) (-1) 0 32 w=((-1)/18)*w 24 + (1)*w 29
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_32

theorem link2_33 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 33 w=rows2 w 33 := by
  change jetBlockRow (1) (-1) 0 33 w=(1)*w 31 + ((-1)/18)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_33

theorem link2_34 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 34 w=rows2 w 34 := by
  change jetBlockRow (1) (-1) 0 34 w=((-18))*w 5 + (1)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_34

theorem link2_35 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 35 w=rows2 w 35 := by
  change jetBlockRow (1) (-1) 0 35 w=((-2)/11)*w 11 + (1)*w 24 + ((-2)/11)*w 33 + (1)*w 46
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_35

theorem link2_36 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 36 w=rows2 w 36 := by
  change jetBlockRow (1) (-1) 0 36 w=(1)*w 20 + ((-2)/11)*w 33 + (1)*w 42 + ((-2)/11)*w 55
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_36

theorem link2_37 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 37 w=rows2 w 37 := by
  change jetBlockRow (1) (-1) 0 37 w=((-1)/2)*w 0 + ((-1)/2)*w 6 + (1)*w 9 + ((-1)/2)*w 12 + (1)*w 15 + ((-1)/2)*w 18 + (1)*w 21 + ((-1)/2)*w 24 + (1)*w 27 + ((-1)/2)*w 30 + (1)*w 33 + ((-1)/2)*w 36 + (1)*w 39 + ((-1)/2)*w 42 + (1)*w 45 + ((-1)/2)*w 48 + (1)*w 51 + ((-1)/2)*w 54 + (1)*w 57 + (1)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_37

theorem link2_38 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 38 w=rows2 w 38 := by
  change jetBlockRow (1) (-1) 0 38 w=((-1)/11)*w 0 + (1)*w 10 + ((-1)/11)*w 22 + (1)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_38

theorem link2_39 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 39 w=rows2 w 39 := by
  change jetBlockRow (1) (-1) 0 39 w=((-1)/11)*w 0 + (1)*w 12 + ((-1)/11)*w 44 + (1)*w 56
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_39

theorem link2_40 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 40 w=rows2 w 40 := by
  change jetBlockRow (1) (-1) 0 40 w=((-1)/22)*w 0 + ((-1)/22)*w 22 + (1)*w 23 + (1)*w 45
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_40

theorem link2_41 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 41 w=rows2 w 41 := by
  change jetBlockRow (1) (-1) 0 41 w=((-1)/22)*w 0 + (1)*w 21 + (1)*w 43 + ((-1)/22)*w 44
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_41

theorem link2_42 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 42 w=rows2 w 42 := by
  change jetBlockRow (1) (-1) 0 42 w=((-1)/18)*w 0 + ((-1)/18)*w 6 + (1)*w 7 + ((-1)/18)*w 12 + (1)*w 13 + ((-1)/18)*w 18 + (1)*w 19 + ((-1)/18)*w 24 + (1)*w 25 + ((-1)/18)*w 30 + (1)*w 31 + ((-1)/18)*w 36 + (1)*w 37 + ((-1)/18)*w 42 + (1)*w 43 + (1)*w 49 + ((-1)/18)*w 54 + (1)*w 55 + ((-1)/18)*w 60 + (1)*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_42

theorem link2_43 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 43 w=rows2 w 43 := by
  change jetBlockRow (1) (-1) 0 43 w=((-2)/9)*w 3 + (1)*w 4 + (1)*w 10 + ((-2)/9)*w 15 + (1)*w 16 + ((-2)/9)*w 21 + (1)*w 22 + ((-2)/9)*w 27 + (1)*w 28 + ((-2)/9)*w 33 + (1)*w 34 + ((-2)/9)*w 39 + (1)*w 40 + ((-2)/9)*w 45 + (1)*w 46 + ((-2)/9)*w 51 + (1)*w 52 + ((-2)/9)*w 57 + (1)*w 58 + ((-2)/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_43

theorem link2_44 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 44 w=rows2 w 44 := by
  change jetBlockRow (1) (-1) 0 44 w=((-2)/9)*w 3 + (1)*w 8 + ((-2)/9)*w 9 + (1)*w 14 + ((-2)/9)*w 15 + (1)*w 20 + ((-2)/9)*w 21 + (1)*w 26 + ((-2)/9)*w 27 + (1)*w 32 + ((-2)/9)*w 33 + (1)*w 38 + ((-2)/9)*w 39 + (1)*w 44 + ((-2)/9)*w 45 + (1)*w 50 + ((-2)/9)*w 51 + (1)*w 56 + (1)*w 62 + ((-2)/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_44

theorem link2_45 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 45 w=rows2 w 45 := by
  change jetBlockRow (1) (-1) 0 45 w=((-1)/18)*w 0 + (1)*w 5 + ((-1)/18)*w 6 + (1)*w 11 + ((-1)/18)*w 12 + (1)*w 17 + (1)*w 23 + ((-1)/18)*w 24 + (1)*w 29 + ((-1)/18)*w 30 + (1)*w 35 + ((-1)/18)*w 36 + (1)*w 41 + ((-1)/18)*w 42 + (1)*w 47 + ((-1)/18)*w 48 + (1)*w 53 + ((-1)/18)*w 54 + (1)*w 59 + ((-1)/18)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_45

theorem link2_46 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 46 w=rows2 w 46 := by
  change jetBlockRow (1) (-1) 0 46 w=(1)*w 0
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_46

theorem link2_47 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 47 w=rows2 w 47 := by
  change jetBlockRow (1) (-1) 0 47 w=(1)*w 22 + (1)*w 44
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_47

theorem link2_48 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 48 w=rows2 w 48 := by
  change jetBlockRow (1) (-1) 0 48 w=(1)*w 11 + (1)*w 55
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_48

theorem link2_49 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 49 w=rows2 w 49 := by
  change jetBlockRow (1) (-1) 0 49 w=(1)*w 6 + (1)*w 12 + (1)*w 18 + (1)*w 24 + (1)*w 30 + (1)*w 36 + (1)*w 42 + (1)*w 48 + (1)*w 54 + (1)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_49

theorem link2_50 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 50 w=rows2 w 50 := by
  change jetBlockRow (1) (-1) 0 50 w=(1)*w 9 + (1/2)*w 18 + (1)*w 42
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_50

theorem link2_51 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 51 w=rows2 w 51 := by
  change jetBlockRow (1) (-1) 0 51 w=(1)*w 15 + (1/2)*w 30 + (1)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_51

theorem link2_52 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 52 w=rows2 w 52 := by
  change jetBlockRow (1) (-1) 0 52 w=(1)*w 16 + (1/2)*w 32 + (1)*w 49
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_52

theorem link2_53 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 53 w=rows2 w 53 := by
  change jetBlockRow (1) (-1) 0 53 w=(1)*w 17 + (1/2)*w 34 + (1)*w 50
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_53

theorem link2_54 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 54 w=rows2 w 54 := by
  change jetBlockRow (1) (-1) 0 54 w=(1)*w 18 + (1/2)*w 36 + (1)*w 51
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_54

theorem link2_55 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 55 w=rows2 w 55 := by
  change jetBlockRow (1) (-1) 0 55 w=(1)*w 5 + (1/2)*w 10 + (1)*w 38
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_55

theorem link2_56 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 56 w=rows2 w 56 := by
  change jetBlockRow (1) (-1) 0 56 w=(1)*w 4 + (1/2)*w 8 + (1)*w 37
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_56

theorem link2_57 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 57 w=rows2 w 57 := by
  change jetBlockRow (1) (-1) 0 57 w=(1)*w 7 + (7/9)*w 21 + (1)*w 29 + (1)*w 51 + (1/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_57

theorem link2_58 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 58 w=rows2 w 58 := by
  change jetBlockRow (1) (-1) 0 58 w=(1)*w 4 + (7/9)*w 12 + (1)*w 26 + (1/9)*w 36 + (1)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_58

theorem link2_59 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 59 w=rows2 w 59 := by
  change jetBlockRow (1) (-1) 0 59 w=(1)*w 13 + (1/2)*w 26 + (1)*w 46
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_59

theorem link2_60 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 60 w=rows2 w 60 := by
  change jetBlockRow (1) (-1) 0 60 w=(1)*w 26 + (1/2)*w 52 + (1)*w 59
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_60

theorem link2_61 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 61 w=rows2 w 61 := by
  change jetBlockRow (1) (-1) 0 61 w=(1)*w 19 + (1/2)*w 38 + (1)*w 52
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_61

theorem link2_62 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 62 w=rows2 w 62 := by
  change jetBlockRow (1) (-1) 0 62 w=(1)*w 5 + (7/9)*w 15 + (1)*w 27 + (1/9)*w 45 + (1)*w 49
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_62

theorem link2_63 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 63 w=rows2 w 63 := by
  change jetBlockRow (1) (-1) 0 63 w=(1)*w 7 + (1/2)*w 14 + (1)*w 40
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_63

theorem link2_64 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 64 w=rows2 w 64 := by
  change jetBlockRow (1) (-1) 0 64 w=(1)*w 8 + (1/2)*w 16 + (1)*w 41
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_64

theorem link2_65 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 65 w=rows2 w 65 := by
  change jetBlockRow (1) (-1) 0 65 w=(1)*w 14 + (1/2)*w 28 + (1)*w 47
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_65

theorem link2_66 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 66 w=rows2 w 66 := by
  change jetBlockRow (1) (-1) 0 66 w=(1)*w 6 + (1/2)*w 12 + (1)*w 39
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_66

theorem link2_67 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 0 67 w=rows2 w 67 := by
  change jetBlockRow (1) (-1) 0 67 w=(1)*w 28 + (1/2)*w 56 + (1)*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_67

theorem link2_68 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 0 w=rows2 w 68 := by
  change jetBlockRow (1) (-1) 1 0 w=((-22))*w 63 + (1)*w 66 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_68

theorem link2_69 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 1 w=rows2 w 69 := by
  change jetBlockRow (1) (-1) 1 1 w=((-1)/3)*w 0 + ((-1))*w 66 + (1)*w 67
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_69

theorem link2_70 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 2 w=rows2 w 70 := by
  change jetBlockRow (1) (-1) 1 2 w=((-1))*w 0 + ((-1))*w 66 + (1)*w 69
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_70

theorem link2_71 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 3 w=rows2 w 71 := by
  change jetBlockRow (1) (-1) 1 3 w=(1/3)*w 0 + ((-1))*w 66 + (1)*w 131
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_71

theorem link2_72 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 4 w=rows2 w 72 := by
  change jetBlockRow (1) (-1) 1 4 w=(330)*w 65 + (1)*w 96 + ((-1))*w 131
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_72

theorem link2_73 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 5 w=rows2 w 73 := by
  change jetBlockRow (1) (-1) 1 5 w=(55)*w 0 + ((-1))*w 66 + (1)*w 99
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_73

theorem link2_74 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 6 w=rows2 w 74 := by
  change jetBlockRow (1) (-1) 1 6 w=((-33))*w 64 + (1)*w 99 + ((-1))*w 130
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_74

theorem link2_75 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 7 w=rows2 w 75 := by
  change jetBlockRow (1) (-1) 1 7 w=((-2)/3)*w 33 + (1)*w 68 + ((-1))*w 99
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_75

theorem link2_76 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 8 w=rows2 w 76 := by
  change jetBlockRow (1) (-1) 1 8 w=((-2))*w 33 + (1)*w 72 + ((-1))*w 99
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_76

theorem link2_77 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 9 w=rows2 w 77 := by
  change jetBlockRow (1) (-1) 1 9 w=((-11))*w 60 + (1)*w 99 + ((-1))*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_77

theorem link2_78 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 10 w=rows2 w 78 := by
  change jetBlockRow (1) (-1) 1 10 w=((-110)/3)*w 63 + (1)*w 100 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_78

theorem link2_79 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 11 w=rows2 w 79 := by
  change jetBlockRow (1) (-1) 1 11 w=(66)*w 65 + (1)*w 98 + ((-1))*w 131
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_79

theorem link2_80 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 12 w=rows2 w 80 := by
  change jetBlockRow (1) (-1) 1 12 w=((-66))*w 63 + (1)*w 102 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_80

theorem link2_81 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 13 w=rows2 w 81 := by
  change jetBlockRow (1) (-1) 1 13 w=((-3))*w 44 + (1)*w 75 + ((-1))*w 110
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_81

theorem link2_82 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 14 w=rows2 w 82 := by
  change jetBlockRow (1) (-1) 1 14 w=((-11)/3)*w 48 + (1)*w 77 + ((-1))*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_82

theorem link2_83 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 15 w=rows2 w 83 := by
  change jetBlockRow (1) (-1) 1 15 w=((-6))*w 55 + (1)*w 84 + ((-1))*w 121
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_83

theorem link2_84 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 16 w=rows2 w 84 := by
  change jetBlockRow (1) (-1) 1 16 w=((-22)/3)*w 57 + (1)*w 88 + ((-1))*w 123
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_84

theorem link2_85 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 17 w=rows2 w 85 := by
  change jetBlockRow (1) (-1) 1 17 w=(66)*w 4 + ((-1))*w 70 + (1)*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_85

theorem link2_86 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 18 w=rows2 w 86 := by
  change jetBlockRow (1) (-1) 1 18 w=(22/3)*w 12 + ((-1))*w 78 + (1)*w 128
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_86

theorem link2_87 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 19 w=rows2 w 87 := by
  change jetBlockRow (1) (-1) 1 19 w=((-33))*w 62 + (1)*w 101 + ((-1))*w 128
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_87

theorem link2_88 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 20 w=rows2 w 88 := by
  change jetBlockRow (1) (-1) 1 20 w=(66)*w 61 + (1)*w 84 + ((-1))*w 127
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_88

theorem link2_89 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 21 w=rows2 w 89 := by
  change jetBlockRow (1) (-1) 1 21 w=(33)*w 62 + (1)*w 93 + ((-1))*w 128
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_89

theorem link2_90 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 22 w=rows2 w 90 := by
  change jetBlockRow (1) (-1) 1 22 w=((-11)/3)*w 42 + (1)*w 103 + ((-1))*w 108
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_90

theorem link2_91 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 23 w=rows2 w 91 := by
  change jetBlockRow (1) (-1) 1 23 w=((-22)/3)*w 51 + (1)*w 104 + ((-1))*w 117
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_91

theorem link2_92 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 24 w=rows2 w 92 := by
  change jetBlockRow (1) (-1) 1 24 w=((-11))*w 54 + (1)*w 105 + ((-1))*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_92

theorem link2_93 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 25 w=rows2 w 93 := by
  change jetBlockRow (1) (-1) 1 25 w=((-22))*w 57 + (1)*w 108 + ((-1))*w 123
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_93

theorem link2_94 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 26 w=rows2 w 94 := by
  change jetBlockRow (1) (-1) 1 26 w=((-33))*w 58 + (1)*w 111 + ((-1))*w 124
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_94

theorem link2_95 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 27 w=rows2 w 95 := by
  change jetBlockRow (1) (-1) 1 27 w=((-66))*w 59 + (1)*w 120 + ((-1))*w 125
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_95

theorem link2_96 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 28 w=rows2 w 96 := by
  change jetBlockRow (1) (-1) 1 28 w=(66)*w 7 + ((-1))*w 73 + (1)*w 78
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_96

theorem link2_97 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 29 w=rows2 w 97 := by
  change jetBlockRow (1) (-1) 1 29 w=(33)*w 8 + ((-1))*w 74 + (1)*w 87
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_97

theorem link2_98 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 30 w=rows2 w 98 := by
  change jetBlockRow (1) (-1) 1 30 w=(22)*w 9 + ((-1))*w 75 + (1)*w 90
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_98

theorem link2_99 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 31 w=rows2 w 99 := by
  change jetBlockRow (1) (-1) 1 31 w=(22/3)*w 15 + ((-1))*w 81 + (1)*w 94
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_99

theorem link2_100 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 32 w=rows2 w 100 := by
  change jetBlockRow (1) (-1) 1 32 w=(11/3)*w 24 + ((-1))*w 90 + (1)*w 95
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_100

theorem link2_101 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 33 w=rows2 w 101 := by
  change jetBlockRow (1) (-1) 1 33 w=((-11)/3)*w 54 + (1)*w 97 + ((-1))*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_101

theorem link2_102 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 34 w=rows2 w 102 := by
  change jetBlockRow (1) (-1) 1 34 w=((-66))*w 5 + ((-1))*w 71 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_102

theorem link2_103 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 35 w=rows2 w 103 := by
  change jetBlockRow (1) (-1) 1 35 w=((-6))*w 11 + ((-6))*w 33 + ((-1))*w 77 + (1)*w 90 + ((-1))*w 99 + (1)*w 112
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_103

theorem link2_104 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 36 w=rows2 w 104 := by
  change jetBlockRow (1) (-1) 1 36 w=(6)*w 33 + (6)*w 55 + (1)*w 86 + ((-1))*w 99 + (1)*w 108 + ((-1))*w 121
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_104

theorem link2_105 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 37 w=rows2 w 105 := by
  change jetBlockRow (1) (-1) 1 37 w=((-11))*w 0 + ((-11))*w 6 + ((-11))*w 12 + ((-11))*w 18 + ((-11))*w 24 + ((-11))*w 30 + ((-11))*w 36 + ((-11))*w 42 + ((-11))*w 48 + ((-11))*w 54 + ((-1))*w 66 + ((-1))*w 72 + (1)*w 75 + ((-1))*w 78 + (1)*w 81 + ((-1))*w 84 + (1)*w 87 + ((-1))*w 90 + (1)*w 93 + ((-1))*w 96 + (1)*w 99 + ((-1))*w 102 + (1)*w 105 + ((-1))*w 108 + (1)*w 111 + ((-1))*w 114 + (1)*w 117 + ((-1))*w 120 + (1)*w 123 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_105

theorem link2_106 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 38 w=rows2 w 106 := by
  change jetBlockRow (1) (-1) 1 38 w=(6)*w 0 + (6)*w 22 + ((-1))*w 66 + (1)*w 76 + ((-1))*w 88 + (1)*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_106

theorem link2_107 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 39 w=rows2 w 107 := by
  change jetBlockRow (1) (-1) 1 39 w=((-6))*w 0 + ((-6))*w 44 + ((-1))*w 66 + (1)*w 78 + ((-1))*w 110 + (1)*w 122
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_107

theorem link2_108 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 40 w=rows2 w 108 := by
  change jetBlockRow (1) (-1) 1 40 w=((-3))*w 0 + ((-3))*w 22 + ((-1))*w 66 + ((-1))*w 88 + (1)*w 89 + (1)*w 111
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_108

theorem link2_109 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 41 w=rows2 w 109 := by
  change jetBlockRow (1) (-1) 1 41 w=(3)*w 0 + (3)*w 44 + ((-1))*w 66 + (1)*w 87 + (1)*w 109 + ((-1))*w 110
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_109

theorem link2_110 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 42 w=rows2 w 110 := by
  change jetBlockRow (1) (-1) 1 42 w=((-11)/3)*w 0 + ((-11)/3)*w 6 + ((-11)/3)*w 12 + ((-11)/3)*w 18 + ((-11)/3)*w 24 + ((-11)/3)*w 30 + ((-11)/3)*w 36 + ((-11)/3)*w 42 + ((-11)/3)*w 54 + ((-11)/3)*w 60 + ((-1))*w 66 + ((-1))*w 72 + (1)*w 73 + ((-1))*w 78 + (1)*w 79 + ((-1))*w 84 + (1)*w 85 + ((-1))*w 90 + (1)*w 91 + ((-1))*w 96 + (1)*w 97 + ((-1))*w 102 + (1)*w 103 + ((-1))*w 108 + (1)*w 109 + (1)*w 115 + ((-1))*w 120 + (1)*w 121 + ((-1))*w 126 + (1)*w 127
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_110

theorem link2_111 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 43 w=rows2 w 111 := by
  change jetBlockRow (1) (-1) 1 43 w=(22/3)*w 3 + (22/3)*w 15 + (22/3)*w 21 + (22/3)*w 27 + (22/3)*w 33 + (22/3)*w 39 + (22/3)*w 45 + (22/3)*w 51 + (22/3)*w 57 + (22/3)*w 63 + ((-1))*w 69 + (1)*w 70 + (1)*w 76 + ((-1))*w 81 + (1)*w 82 + ((-1))*w 87 + (1)*w 88 + ((-1))*w 93 + (1)*w 94 + ((-1))*w 99 + (1)*w 100 + ((-1))*w 105 + (1)*w 106 + ((-1))*w 111 + (1)*w 112 + ((-1))*w 117 + (1)*w 118 + ((-1))*w 123 + (1)*w 124 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_111

theorem link2_112 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 44 w=rows2 w 112 := by
  change jetBlockRow (1) (-1) 1 44 w=((-22)/3)*w 3 + ((-22)/3)*w 9 + ((-22)/3)*w 15 + ((-22)/3)*w 21 + ((-22)/3)*w 27 + ((-22)/3)*w 33 + ((-22)/3)*w 39 + ((-22)/3)*w 45 + ((-22)/3)*w 51 + ((-22)/3)*w 63 + ((-1))*w 69 + (1)*w 74 + ((-1))*w 75 + (1)*w 80 + ((-1))*w 81 + (1)*w 86 + ((-1))*w 87 + (1)*w 92 + ((-1))*w 93 + (1)*w 98 + ((-1))*w 99 + (1)*w 104 + ((-1))*w 105 + (1)*w 110 + ((-1))*w 111 + (1)*w 116 + ((-1))*w 117 + (1)*w 122 + (1)*w 128 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_112

theorem link2_113 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 45 w=rows2 w 113 := by
  change jetBlockRow (1) (-1) 1 45 w=(11/3)*w 0 + (11/3)*w 6 + (11/3)*w 12 + (11/3)*w 24 + (11/3)*w 30 + (11/3)*w 36 + (11/3)*w 42 + (11/3)*w 48 + (11/3)*w 54 + (11/3)*w 60 + ((-1))*w 66 + (1)*w 71 + ((-1))*w 72 + (1)*w 77 + ((-1))*w 78 + (1)*w 83 + (1)*w 89 + ((-1))*w 90 + (1)*w 95 + ((-1))*w 96 + (1)*w 101 + ((-1))*w 102 + (1)*w 107 + ((-1))*w 108 + (1)*w 113 + ((-1))*w 114 + (1)*w 119 + ((-1))*w 120 + (1)*w 125 + ((-1))*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_113

theorem link2_114 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 46 w=rows2 w 114 := by
  change jetBlockRow (1) (-1) 1 46 w=(1)*w 66
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_114

theorem link2_115 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 47 w=rows2 w 115 := by
  change jetBlockRow (1) (-1) 1 47 w=(1)*w 88 + (1)*w 110
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_115

theorem link2_116 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 48 w=rows2 w 116 := by
  change jetBlockRow (1) (-1) 1 48 w=(1)*w 77 + (1)*w 121
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_116

theorem link2_117 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 49 w=rows2 w 117 := by
  change jetBlockRow (1) (-1) 1 49 w=(1)*w 72 + (1)*w 78 + (1)*w 84 + (1)*w 90 + (1)*w 96 + (1)*w 102 + (1)*w 108 + (1)*w 114 + (1)*w 120 + (1)*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_117

theorem link2_118 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 50 w=rows2 w 118 := by
  change jetBlockRow (1) (-1) 1 50 w=(1)*w 75 + (1)*w 84 + (1)*w 108
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_118

theorem link2_119 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 51 w=rows2 w 119 := by
  change jetBlockRow (1) (-1) 1 51 w=(1)*w 81 + (1)*w 96 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_119

theorem link2_120 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 52 w=rows2 w 120 := by
  change jetBlockRow (1) (-1) 1 52 w=(1)*w 82 + (1)*w 98 + (1)*w 115
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_120

theorem link2_121 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 53 w=rows2 w 121 := by
  change jetBlockRow (1) (-1) 1 53 w=(1)*w 83 + (1)*w 100 + (1)*w 116
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_121

theorem link2_122 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 54 w=rows2 w 122 := by
  change jetBlockRow (1) (-1) 1 54 w=(1)*w 84 + (1)*w 102 + (1)*w 117
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_122

theorem link2_123 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 55 w=rows2 w 123 := by
  change jetBlockRow (1) (-1) 1 55 w=(1)*w 71 + (1)*w 76 + (1)*w 104
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_123

theorem link2_124 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 56 w=rows2 w 124 := by
  change jetBlockRow (1) (-1) 1 56 w=(1)*w 70 + (1)*w 74 + (1)*w 103
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_124

theorem link2_125 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 57 w=rows2 w 125 := by
  change jetBlockRow (1) (-1) 1 57 w=(1)*w 73 + (7/3)*w 87 + (1)*w 95 + (1)*w 117 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_125

theorem link2_126 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 58 w=rows2 w 126 := by
  change jetBlockRow (1) (-1) 1 58 w=(1)*w 70 + (7/3)*w 78 + (1)*w 92 + (1)*w 102 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_126

theorem link2_127 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 59 w=rows2 w 127 := by
  change jetBlockRow (1) (-1) 1 59 w=(1)*w 79 + (1)*w 92 + (1)*w 112
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_127

theorem link2_128 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 60 w=rows2 w 128 := by
  change jetBlockRow (1) (-1) 1 60 w=(1)*w 92 + (1)*w 118 + (1)*w 125
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_128

theorem link2_129 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 61 w=rows2 w 129 := by
  change jetBlockRow (1) (-1) 1 61 w=(1)*w 85 + (1)*w 104 + (1)*w 118
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_129

theorem link2_130 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 62 w=rows2 w 130 := by
  change jetBlockRow (1) (-1) 1 62 w=(1)*w 71 + (7/3)*w 81 + (1)*w 93 + (1)*w 111 + (1)*w 115
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_130

theorem link2_131 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 63 w=rows2 w 131 := by
  change jetBlockRow (1) (-1) 1 63 w=(1)*w 73 + (1)*w 80 + (1)*w 106
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_131

theorem link2_132 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 64 w=rows2 w 132 := by
  change jetBlockRow (1) (-1) 1 64 w=(1)*w 74 + (1)*w 82 + (1)*w 107
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_132

theorem link2_133 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 65 w=rows2 w 133 := by
  change jetBlockRow (1) (-1) 1 65 w=(1)*w 80 + (1)*w 94 + (1)*w 113
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_133

theorem link2_134 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 66 w=rows2 w 134 := by
  change jetBlockRow (1) (-1) 1 66 w=(1)*w 72 + (1)*w 78 + (1)*w 105
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_134

theorem link2_135 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 1 67 w=rows2 w 135 := by
  change jetBlockRow (1) (-1) 1 67 w=(1)*w 94 + (1)*w 122 + (1)*w 127
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_135

theorem link2_136 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 0 w=rows2 w 136 := by
  change jetBlockRow (1) (-1) 2 0 w=((-11))*w 63 + ((-1))*w 129 + (1)*w 132 + ((-1)/22)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_136

theorem link2_137 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 1 w=rows2 w 137 := by
  change jetBlockRow (1) (-1) 2 1 w=((-11))*w 0 + ((-66))*w 66 + ((-198))*w 132 + (1)*w 133
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_137

theorem link2_138 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 2 w=rows2 w 138 := by
  change jetBlockRow (1) (-1) 2 2 w=((-11))*w 0 + ((-22))*w 66 + ((-22))*w 132 + (1)*w 135
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_138

theorem link2_139 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 3 w=rows2 w 139 := by
  change jetBlockRow (1) (-1) 2 3 w=((-11))*w 0 + (66)*w 66 + ((-198))*w 132 + (1)*w 197
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_139

theorem link2_140 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 4 w=rows2 w 140 := by
  change jetBlockRow (1) (-1) 2 4 w=((-3025))*w 65 + (55/3)*w 131 + (1)*w 162 + ((-1)/18)*w 197
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_140

theorem link2_141 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 5 w=rows2 w 141 := by
  change jetBlockRow (1) (-1) 2 5 w=((-3025))*w 0 + (110)*w 66 + ((-2))*w 132 + (1)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_141

theorem link2_142 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 6 w=rows2 w 142 := by
  change jetBlockRow (1) (-1) 2 6 w=((-11))*w 64 + ((-2)/3)*w 130 + (1)*w 165 + ((-2)/99)*w 196
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_142

theorem link2_143 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 7 w=rows2 w 143 := by
  change jetBlockRow (1) (-1) 2 7 w=((-11))*w 33 + ((-33))*w 99 + (1)*w 134 + ((-99)/2)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_143

theorem link2_144 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 8 w=rows2 w 144 := by
  change jetBlockRow (1) (-1) 2 8 w=((-11))*w 33 + ((-11))*w 99 + (1)*w 138 + ((-11)/2)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_144

theorem link2_145 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 9 w=rows2 w 145 := by
  change jetBlockRow (1) (-1) 2 9 w=((-11))*w 60 + ((-2))*w 126 + (1)*w 165 + ((-2)/11)*w 192
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_145

theorem link2_146 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 10 w=rows2 w 146 := by
  change jetBlockRow (1) (-1) 2 10 w=((-3025))*w 63 + ((-165))*w 129 + (1)*w 166 + ((-9)/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_146

theorem link2_147 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 11 w=rows2 w 147 := by
  change jetBlockRow (1) (-1) 2 11 w=((-1089))*w 65 + (33)*w 131 + (1)*w 164 + ((-1)/2)*w 197
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_147

theorem link2_148 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 12 w=rows2 w 148 := by
  change jetBlockRow (1) (-1) 2 12 w=((-1089))*w 63 + ((-33))*w 129 + (1)*w 168 + ((-1)/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_148

theorem link2_149 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 13 w=rows2 w 149 := by
  change jetBlockRow (1) (-1) 2 13 w=((-11))*w 44 + ((-22)/3)*w 110 + (1)*w 141 + ((-22)/9)*w 176
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_149

theorem link2_150 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 14 w=rows2 w 150 := by
  change jetBlockRow (1) (-1) 2 14 w=((-11))*w 48 + ((-6))*w 114 + (1)*w 143 + ((-18)/11)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_150

theorem link2_151 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 15 w=rows2 w 151 := by
  change jetBlockRow (1) (-1) 2 15 w=((-11))*w 55 + ((-11)/3)*w 121 + (1)*w 150 + ((-11)/18)*w 187
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_151

theorem link2_152 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 16 w=rows2 w 152 := by
  change jetBlockRow (1) (-1) 2 16 w=((-11))*w 57 + ((-3))*w 123 + (1)*w 154 + ((-9)/22)*w 189
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_152

theorem link2_153 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 17 w=rows2 w 153 := by
  change jetBlockRow (1) (-1) 2 17 w=((-242))*w 4 + (22/3)*w 70 + ((-1)/9)*w 136 + (1)*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_153

theorem link2_154 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 18 w=rows2 w 154 := by
  change jetBlockRow (1) (-1) 2 18 w=((-242))*w 12 + (66)*w 78 + ((-9))*w 144 + (1)*w 194
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_154

theorem link2_155 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 19 w=rows2 w 155 := by
  change jetBlockRow (1) (-1) 2 19 w=((-1089))*w 62 + ((-66))*w 128 + (1)*w 167 + ((-2))*w 194
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_155

theorem link2_156 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 20 w=rows2 w 156 := by
  change jetBlockRow (1) (-1) 2 20 w=((-121))*w 61 + (11/3)*w 127 + (1)*w 150 + ((-1)/18)*w 193
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_156

theorem link2_157 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 21 w=rows2 w 157 := by
  change jetBlockRow (1) (-1) 2 21 w=((-121))*w 62 + (22/3)*w 128 + (1)*w 159 + ((-2)/9)*w 194
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_157

theorem link2_158 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 22 w=rows2 w 158 := by
  change jetBlockRow (1) (-1) 2 22 w=((-121))*w 42 + ((-66))*w 108 + (1)*w 169 + ((-18))*w 174
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_158

theorem link2_159 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 23 w=rows2 w 159 := by
  change jetBlockRow (1) (-1) 2 23 w=((-121))*w 51 + ((-33))*w 117 + (1)*w 170 + ((-9)/2)*w 183
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_159

theorem link2_160 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 24 w=rows2 w 160 := by
  change jetBlockRow (1) (-1) 2 24 w=((-121))*w 54 + ((-22))*w 120 + (1)*w 171 + ((-2))*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_160

theorem link2_161 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 25 w=rows2 w 161 := by
  change jetBlockRow (1) (-1) 2 25 w=((-121))*w 57 + ((-11))*w 123 + (1)*w 174 + ((-1)/2)*w 189
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_161

theorem link2_162 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 26 w=rows2 w 162 := by
  change jetBlockRow (1) (-1) 2 26 w=((-121))*w 58 + ((-22)/3)*w 124 + (1)*w 177 + ((-2)/9)*w 190
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_162

theorem link2_163 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 27 w=rows2 w 163 := by
  change jetBlockRow (1) (-1) 2 27 w=((-121))*w 59 + ((-11)/3)*w 125 + (1)*w 186 + ((-1)/18)*w 191
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_163

theorem link2_164 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 28 w=rows2 w 164 := by
  change jetBlockRow (1) (-1) 2 28 w=((-121))*w 7 + (11/3)*w 73 + ((-1)/18)*w 139 + (1)*w 144
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_164

theorem link2_165 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 29 w=rows2 w 165 := by
  change jetBlockRow (1) (-1) 2 29 w=((-121))*w 8 + (22/3)*w 74 + ((-2)/9)*w 140 + (1)*w 153
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_165

theorem link2_166 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 30 w=rows2 w 166 := by
  change jetBlockRow (1) (-1) 2 30 w=((-121))*w 9 + (11)*w 75 + ((-1)/2)*w 141 + (1)*w 156
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_166

theorem link2_167 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 31 w=rows2 w 167 := by
  change jetBlockRow (1) (-1) 2 31 w=((-121))*w 15 + (33)*w 81 + ((-9)/2)*w 147 + (1)*w 160
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_167

theorem link2_168 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 32 w=rows2 w 168 := by
  change jetBlockRow (1) (-1) 2 32 w=((-121))*w 24 + (66)*w 90 + ((-18))*w 156 + (1)*w 161
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_168

theorem link2_169 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 33 w=rows2 w 169 := by
  change jetBlockRow (1) (-1) 2 33 w=((-121))*w 54 + ((-66))*w 120 + (1)*w 163 + ((-18))*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_169

theorem link2_170 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 34 w=rows2 w 170 := by
  change jetBlockRow (1) (-1) 2 34 w=((-121))*w 5 + ((-11)/3)*w 71 + ((-1)/18)*w 137 + (1)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_170

theorem link2_171 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 35 w=rows2 w 171 := by
  change jetBlockRow (1) (-1) 2 35 w=((-99))*w 11 + ((-99))*w 33 + ((-33))*w 77 + ((-33))*w 99 + ((-11)/2)*w 143 + (1)*w 156 + ((-11)/2)*w 165 + (1)*w 178
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_171

theorem link2_172 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 36 w=rows2 w 172 := by
  change jetBlockRow (1) (-1) 2 36 w=((-99))*w 33 + ((-99))*w 55 + (33)*w 99 + (33)*w 121 + (1)*w 152 + ((-11)/2)*w 165 + (1)*w 174 + ((-11)/2)*w 187
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_172

theorem link2_173 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 37 w=rows2 w 173 := by
  change jetBlockRow (1) (-1) 2 37 w=((-121))*w 0 + ((-121))*w 6 + ((-121))*w 12 + ((-121))*w 18 + ((-121))*w 24 + ((-121))*w 30 + ((-121))*w 36 + ((-121))*w 42 + ((-121))*w 48 + ((-121))*w 54 + ((-22))*w 66 + ((-22))*w 72 + ((-22))*w 78 + ((-22))*w 84 + ((-22))*w 90 + ((-22))*w 96 + ((-22))*w 102 + ((-22))*w 108 + ((-22))*w 114 + ((-22))*w 120 + ((-2))*w 132 + ((-2))*w 138 + (1)*w 141 + ((-2))*w 144 + (1)*w 147 + ((-2))*w 150 + (1)*w 153 + ((-2))*w 156 + (1)*w 159 + ((-2))*w 162 + (1)*w 165 + ((-2))*w 168 + (1)*w 171 + ((-2))*w 174 + (1)*w 177 + ((-2))*w 180 + (1)*w 183 + ((-2))*w 186 + (1)*w 189 + (1)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_173

theorem link2_174 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 38 w=rows2 w 174 := by
  change jetBlockRow (1) (-1) 2 38 w=((-198))*w 0 + ((-198))*w 22 + (66)*w 66 + (66)*w 88 + ((-11))*w 132 + (1)*w 142 + ((-11))*w 154 + (1)*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_174

theorem link2_175 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 39 w=rows2 w 175 := by
  change jetBlockRow (1) (-1) 2 39 w=((-198))*w 0 + ((-198))*w 44 + ((-66))*w 66 + ((-66))*w 110 + ((-11))*w 132 + (1)*w 144 + ((-11))*w 176 + (1)*w 188
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_175

theorem link2_176 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 40 w=rows2 w 176 := by
  change jetBlockRow (1) (-1) 2 40 w=((-99))*w 0 + ((-99))*w 22 + ((-66))*w 66 + ((-66))*w 88 + ((-22))*w 132 + ((-22))*w 154 + (1)*w 155 + (1)*w 177
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_176

theorem link2_177 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 41 w=rows2 w 177 := by
  change jetBlockRow (1) (-1) 2 41 w=((-99))*w 0 + ((-99))*w 44 + (66)*w 66 + (66)*w 110 + ((-22))*w 132 + (1)*w 153 + (1)*w 175 + ((-22))*w 176
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_177

theorem link2_178 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 42 w=rows2 w 178 := by
  change jetBlockRow (1) (-1) 2 42 w=((-121))*w 0 + ((-121))*w 6 + ((-121))*w 12 + ((-121))*w 18 + ((-121))*w 24 + ((-121))*w 30 + ((-121))*w 36 + ((-121))*w 42 + ((-121))*w 54 + ((-121))*w 60 + ((-66))*w 66 + ((-66))*w 72 + ((-66))*w 78 + ((-66))*w 84 + ((-66))*w 90 + ((-66))*w 96 + ((-66))*w 102 + ((-66))*w 108 + ((-66))*w 120 + ((-66))*w 126 + ((-18))*w 132 + ((-18))*w 138 + (1)*w 139 + ((-18))*w 144 + (1)*w 145 + ((-18))*w 150 + (1)*w 151 + ((-18))*w 156 + (1)*w 157 + ((-18))*w 162 + (1)*w 163 + ((-18))*w 168 + (1)*w 169 + ((-18))*w 174 + (1)*w 175 + (1)*w 181 + ((-18))*w 186 + (1)*w 187 + ((-18))*w 192 + (1)*w 193
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_178

theorem link2_179 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 43 w=rows2 w 179 := by
  change jetBlockRow (1) (-1) 2 43 w=((-121))*w 3 + ((-121))*w 15 + ((-121))*w 21 + ((-121))*w 27 + ((-121))*w 33 + ((-121))*w 39 + ((-121))*w 45 + ((-121))*w 51 + ((-121))*w 57 + ((-121))*w 63 + (33)*w 69 + (33)*w 81 + (33)*w 87 + (33)*w 93 + (33)*w 99 + (33)*w 105 + (33)*w 111 + (33)*w 117 + (33)*w 123 + (33)*w 129 + ((-9)/2)*w 135 + (1)*w 136 + (1)*w 142 + ((-9)/2)*w 147 + (1)*w 148 + ((-9)/2)*w 153 + (1)*w 154 + ((-9)/2)*w 159 + (1)*w 160 + ((-9)/2)*w 165 + (1)*w 166 + ((-9)/2)*w 171 + (1)*w 172 + ((-9)/2)*w 177 + (1)*w 178 + ((-9)/2)*w 183 + (1)*w 184 + ((-9)/2)*w 189 + (1)*w 190 + ((-9)/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_179

theorem link2_180 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 44 w=rows2 w 180 := by
  change jetBlockRow (1) (-1) 2 44 w=((-121))*w 3 + ((-121))*w 9 + ((-121))*w 15 + ((-121))*w 21 + ((-121))*w 27 + ((-121))*w 33 + ((-121))*w 39 + ((-121))*w 45 + ((-121))*w 51 + ((-121))*w 63 + ((-33))*w 69 + ((-33))*w 75 + ((-33))*w 81 + ((-33))*w 87 + ((-33))*w 93 + ((-33))*w 99 + ((-33))*w 105 + ((-33))*w 111 + ((-33))*w 117 + ((-33))*w 129 + ((-9)/2)*w 135 + (1)*w 140 + ((-9)/2)*w 141 + (1)*w 146 + ((-9)/2)*w 147 + (1)*w 152 + ((-9)/2)*w 153 + (1)*w 158 + ((-9)/2)*w 159 + (1)*w 164 + ((-9)/2)*w 165 + (1)*w 170 + ((-9)/2)*w 171 + (1)*w 176 + ((-9)/2)*w 177 + (1)*w 182 + ((-9)/2)*w 183 + (1)*w 188 + (1)*w 194 + ((-9)/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_180

theorem link2_181 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 45 w=rows2 w 181 := by
  change jetBlockRow (1) (-1) 2 45 w=((-121))*w 0 + ((-121))*w 6 + ((-121))*w 12 + ((-121))*w 24 + ((-121))*w 30 + ((-121))*w 36 + ((-121))*w 42 + ((-121))*w 48 + ((-121))*w 54 + ((-121))*w 60 + (66)*w 66 + (66)*w 72 + (66)*w 78 + (66)*w 90 + (66)*w 96 + (66)*w 102 + (66)*w 108 + (66)*w 114 + (66)*w 120 + (66)*w 126 + ((-18))*w 132 + (1)*w 137 + ((-18))*w 138 + (1)*w 143 + ((-18))*w 144 + (1)*w 149 + (1)*w 155 + ((-18))*w 156 + (1)*w 161 + ((-18))*w 162 + (1)*w 167 + ((-18))*w 168 + (1)*w 173 + ((-18))*w 174 + (1)*w 179 + ((-18))*w 180 + (1)*w 185 + ((-18))*w 186 + (1)*w 191 + ((-18))*w 192
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_181

theorem link2_182 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 46 w=rows2 w 182 := by
  change jetBlockRow (1) (-1) 2 46 w=(1)*w 132
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_182

theorem link2_183 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 47 w=rows2 w 183 := by
  change jetBlockRow (1) (-1) 2 47 w=(1)*w 154 + (1)*w 176
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_183

theorem link2_184 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 48 w=rows2 w 184 := by
  change jetBlockRow (1) (-1) 2 48 w=(1)*w 143 + (1)*w 187
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_184

theorem link2_185 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 49 w=rows2 w 185 := by
  change jetBlockRow (1) (-1) 2 49 w=(1)*w 138 + (1)*w 144 + (1)*w 150 + (1)*w 156 + (1)*w 162 + (1)*w 168 + (1)*w 174 + (1)*w 180 + (1)*w 186 + (1)*w 192
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_185

theorem link2_186 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 50 w=rows2 w 186 := by
  change jetBlockRow (1) (-1) 2 50 w=(1)*w 141 + (2)*w 150 + (1)*w 174
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_186

theorem link2_187 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 51 w=rows2 w 187 := by
  change jetBlockRow (1) (-1) 2 51 w=(1)*w 147 + (2)*w 162 + (1)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_187

theorem link2_188 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 52 w=rows2 w 188 := by
  change jetBlockRow (1) (-1) 2 52 w=(1)*w 148 + (2)*w 164 + (1)*w 181
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_188

theorem link2_189 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 53 w=rows2 w 189 := by
  change jetBlockRow (1) (-1) 2 53 w=(1)*w 149 + (2)*w 166 + (1)*w 182
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_189

theorem link2_190 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 54 w=rows2 w 190 := by
  change jetBlockRow (1) (-1) 2 54 w=(1)*w 150 + (2)*w 168 + (1)*w 183
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_190

theorem link2_191 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 55 w=rows2 w 191 := by
  change jetBlockRow (1) (-1) 2 55 w=(1)*w 137 + (2)*w 142 + (1)*w 170
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_191

theorem link2_192 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 56 w=rows2 w 192 := by
  change jetBlockRow (1) (-1) 2 56 w=(1)*w 136 + (2)*w 140 + (1)*w 169
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_192

theorem link2_193 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 57 w=rows2 w 193 := by
  change jetBlockRow (1) (-1) 2 57 w=(1)*w 139 + (7)*w 153 + (1)*w 161 + (1)*w 183 + (9)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_193

theorem link2_194 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 58 w=rows2 w 194 := by
  change jetBlockRow (1) (-1) 2 58 w=(1)*w 136 + (7)*w 144 + (1)*w 158 + (9)*w 168 + (1)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_194

theorem link2_195 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 59 w=rows2 w 195 := by
  change jetBlockRow (1) (-1) 2 59 w=(1)*w 145 + (2)*w 158 + (1)*w 178
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_195

theorem link2_196 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 60 w=rows2 w 196 := by
  change jetBlockRow (1) (-1) 2 60 w=(1)*w 158 + (2)*w 184 + (1)*w 191
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_196

theorem link2_197 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 61 w=rows2 w 197 := by
  change jetBlockRow (1) (-1) 2 61 w=(1)*w 151 + (2)*w 170 + (1)*w 184
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_197

theorem link2_198 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 62 w=rows2 w 198 := by
  change jetBlockRow (1) (-1) 2 62 w=(1)*w 137 + (7)*w 147 + (1)*w 159 + (9)*w 177 + (1)*w 181
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_198

theorem link2_199 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 63 w=rows2 w 199 := by
  change jetBlockRow (1) (-1) 2 63 w=(1)*w 139 + (2)*w 146 + (1)*w 172
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_199

theorem link2_200 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 64 w=rows2 w 200 := by
  change jetBlockRow (1) (-1) 2 64 w=(1)*w 140 + (2)*w 148 + (1)*w 173
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_200

theorem link2_201 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 65 w=rows2 w 201 := by
  change jetBlockRow (1) (-1) 2 65 w=(1)*w 146 + (2)*w 160 + (1)*w 179
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_201

theorem link2_202 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 66 w=rows2 w 202 := by
  change jetBlockRow (1) (-1) 2 66 w=(1)*w 138 + (2)*w 144 + (1)*w 171
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_202

theorem link2_203 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 2 67 w=rows2 w 203 := by
  change jetBlockRow (1) (-1) 2 67 w=(1)*w 160 + (2)*w 188 + (1)*w 193
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_203

theorem link2_204 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 0 w=rows2 w 204 := by
  change jetBlockRow (1) (-1) 3 0 w=((-11)/3)*w 63 + ((-1)/2)*w 129 + ((-1)/22)*w 195 + (1)*w 198 + ((-1)/484)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_204

theorem link2_205 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 1 w=rows2 w 205 := by
  change jetBlockRow (1) (-1) 3 1 w=((-242))*w 0 + ((-2178))*w 66 + ((-13068))*w 132 + ((-39204))*w 198 + (1)*w 199
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_205

theorem link2_206 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 2 w=rows2 w 206 := by
  change jetBlockRow (1) (-1) 3 2 w=((-242)/3)*w 0 + ((-242))*w 66 + ((-484))*w 132 + ((-484))*w 198 + (1)*w 201
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_206

theorem link2_207 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 3 w=rows2 w 207 := by
  change jetBlockRow (1) (-1) 3 3 w=(242)*w 0 + ((-2178))*w 66 + (13068)*w 132 + ((-39204))*w 198 + (1)*w 263
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_207

theorem link2_208 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 4 w=rows2 w 208 := by
  change jetBlockRow (1) (-1) 3 4 w=(166375/9)*w 65 + ((-3025)/18)*w 131 + (55/54)*w 197 + (1)*w 228 + ((-1)/324)*w 263
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_208

theorem link2_209 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 5 w=rows2 w 209 := by
  change jetBlockRow (1) (-1) 3 5 w=(332750/3)*w 0 + ((-6050))*w 66 + (220)*w 132 + ((-4))*w 198 + (1)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_209

theorem link2_210 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 6 w=rows2 w 210 := by
  change jetBlockRow (1) (-1) 3 6 w=((-22)/9)*w 64 + ((-2)/9)*w 130 + ((-4)/297)*w 196 + (1)*w 231 + ((-4)/9801)*w 262
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_210

theorem link2_211 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 7 w=rows2 w 211 := by
  change jetBlockRow (1) (-1) 3 7 w=((-121))*w 33 + ((-1089)/2)*w 99 + ((-3267)/2)*w 165 + (1)*w 200 + ((-9801)/4)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_211

theorem link2_212 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 8 w=rows2 w 212 := by
  change jetBlockRow (1) (-1) 3 8 w=((-121)/3)*w 33 + ((-121)/2)*w 99 + ((-121)/2)*w 165 + (1)*w 204 + ((-121)/4)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_212

theorem link2_213 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 9 w=rows2 w 213 := by
  change jetBlockRow (1) (-1) 3 9 w=((-22)/3)*w 60 + ((-2))*w 126 + ((-4)/11)*w 192 + (1)*w 231 + ((-4)/121)*w 258
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_213

theorem link2_214 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 10 w=rows2 w 214 := by
  change jetBlockRow (1) (-1) 3 10 w=((-166375))*w 63 + ((-27225)/2)*w 129 + ((-1485)/2)*w 195 + (1)*w 232 + ((-81)/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_214

theorem link2_215 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 11 w=rows2 w 215 := by
  change jetBlockRow (1) (-1) 3 11 w=(11979)*w 65 + ((-1089)/2)*w 131 + (33/2)*w 197 + (1)*w 230 + ((-1)/4)*w 263
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_215

theorem link2_216 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 12 w=rows2 w 216 := by
  change jetBlockRow (1) (-1) 3 12 w=((-11979))*w 63 + ((-1089)/2)*w 129 + ((-33)/2)*w 195 + (1)*w 234 + ((-1)/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_216

theorem link2_217 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 13 w=rows2 w 217 := by
  change jetBlockRow (1) (-1) 3 13 w=((-242)/9)*w 44 + ((-242)/9)*w 110 + ((-484)/27)*w 176 + (1)*w 207 + ((-484)/81)*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_217

theorem link2_218 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 14 w=rows2 w 218 := by
  change jetBlockRow (1) (-1) 3 14 w=((-22))*w 48 + ((-18))*w 114 + ((-108)/11)*w 180 + (1)*w 209 + ((-324)/121)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_218

theorem link2_219 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 15 w=rows2 w 219 := by
  change jetBlockRow (1) (-1) 3 15 w=((-121)/9)*w 55 + ((-121)/18)*w 121 + ((-121)/54)*w 187 + (1)*w 216 + ((-121)/324)*w 253
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_219

theorem link2_220 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 16 w=rows2 w 220 := by
  change jetBlockRow (1) (-1) 3 16 w=((-11))*w 57 + ((-9)/2)*w 123 + ((-27)/22)*w 189 + (1)*w 220 + ((-81)/484)*w 255
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_220

theorem link2_221 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 17 w=rows2 w 221 := by
  change jetBlockRow (1) (-1) 3 17 w=(5324/9)*w 4 + ((-242)/9)*w 70 + (22/27)*w 136 + ((-1)/81)*w 202 + (1)*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_221

theorem link2_222 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 18 w=rows2 w 222 := by
  change jetBlockRow (1) (-1) 3 18 w=(5324)*w 12 + ((-2178))*w 78 + (594)*w 144 + ((-81))*w 210 + (1)*w 260
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_222

theorem link2_223 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 19 w=rows2 w 223 := by
  change jetBlockRow (1) (-1) 3 19 w=((-23958))*w 62 + ((-2178))*w 128 + ((-132))*w 194 + (1)*w 233 + ((-4))*w 260
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_223

theorem link2_224 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 20 w=rows2 w 224 := by
  change jetBlockRow (1) (-1) 3 20 w=(1331/9)*w 61 + ((-121)/18)*w 127 + (11/54)*w 193 + (1)*w 216 + ((-1)/324)*w 259
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_224

theorem link2_225 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 21 w=rows2 w 225 := by
  change jetBlockRow (1) (-1) 3 21 w=(2662/9)*w 62 + ((-242)/9)*w 128 + (44/27)*w 194 + (1)*w 225 + ((-4)/81)*w 260
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_225

theorem link2_226 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 22 w=rows2 w 226 := by
  change jetBlockRow (1) (-1) 3 22 w=((-2662))*w 42 + ((-2178))*w 108 + ((-1188))*w 174 + (1)*w 235 + ((-324))*w 240
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_226

theorem link2_227 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 23 w=rows2 w 227 := by
  change jetBlockRow (1) (-1) 3 23 w=((-1331))*w 51 + ((-1089)/2)*w 117 + ((-297)/2)*w 183 + (1)*w 236 + ((-81)/4)*w 249
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_227

theorem link2_228 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 24 w=rows2 w 228 := by
  change jetBlockRow (1) (-1) 3 24 w=((-2662)/3)*w 54 + ((-242))*w 120 + ((-44))*w 186 + (1)*w 237 + ((-4))*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_228

theorem link2_229 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 25 w=rows2 w 229 := by
  change jetBlockRow (1) (-1) 3 25 w=((-1331)/3)*w 57 + ((-121)/2)*w 123 + ((-11)/2)*w 189 + (1)*w 240 + ((-1)/4)*w 255
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_229

theorem link2_230 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 26 w=rows2 w 230 := by
  change jetBlockRow (1) (-1) 3 26 w=((-2662)/9)*w 58 + ((-242)/9)*w 124 + ((-44)/27)*w 190 + (1)*w 243 + ((-4)/81)*w 256
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_230

theorem link2_231 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 27 w=rows2 w 231 := by
  change jetBlockRow (1) (-1) 3 27 w=((-1331)/9)*w 59 + ((-121)/18)*w 125 + ((-11)/54)*w 191 + (1)*w 252 + ((-1)/324)*w 257
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_231

theorem link2_232 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 28 w=rows2 w 232 := by
  change jetBlockRow (1) (-1) 3 28 w=(1331/9)*w 7 + ((-121)/18)*w 73 + (11/54)*w 139 + ((-1)/324)*w 205 + (1)*w 210
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_232

theorem link2_233 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 29 w=rows2 w 233 := by
  change jetBlockRow (1) (-1) 3 29 w=(2662/9)*w 8 + ((-242)/9)*w 74 + (44/27)*w 140 + ((-4)/81)*w 206 + (1)*w 219
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_233

theorem link2_234 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 30 w=rows2 w 234 := by
  change jetBlockRow (1) (-1) 3 30 w=(1331/3)*w 9 + ((-121)/2)*w 75 + (11/2)*w 141 + ((-1)/4)*w 207 + (1)*w 222
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_234

theorem link2_235 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 31 w=rows2 w 235 := by
  change jetBlockRow (1) (-1) 3 31 w=(1331)*w 15 + ((-1089)/2)*w 81 + (297/2)*w 147 + ((-81)/4)*w 213 + (1)*w 226
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_235

theorem link2_236 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 32 w=rows2 w 236 := by
  change jetBlockRow (1) (-1) 3 32 w=(2662)*w 24 + ((-2178))*w 90 + (1188)*w 156 + ((-324))*w 222 + (1)*w 227
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_236

theorem link2_237 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 33 w=rows2 w 237 := by
  change jetBlockRow (1) (-1) 3 33 w=((-2662))*w 54 + ((-2178))*w 120 + ((-1188))*w 186 + (1)*w 229 + ((-324))*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_237

theorem link2_238 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 34 w=rows2 w 238 := by
  change jetBlockRow (1) (-1) 3 34 w=((-1331)/9)*w 5 + ((-121)/18)*w 71 + ((-11)/54)*w 137 + ((-1)/324)*w 203 + (1)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_238

theorem link2_239 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 35 w=rows2 w 239 := by
  change jetBlockRow (1) (-1) 3 35 w=((-1089))*w 11 + ((-1089))*w 33 + ((-1089)/2)*w 77 + ((-1089)/2)*w 99 + ((-363)/2)*w 143 + ((-363)/2)*w 165 + ((-121)/4)*w 209 + (1)*w 222 + ((-121)/4)*w 231 + (1)*w 244
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_239

theorem link2_240 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 36 w=rows2 w 240 := by
  change jetBlockRow (1) (-1) 3 36 w=(1089)*w 33 + (1089)*w 55 + ((-1089)/2)*w 99 + ((-1089)/2)*w 121 + (363/2)*w 165 + (363/2)*w 187 + (1)*w 218 + ((-121)/4)*w 231 + (1)*w 240 + ((-121)/4)*w 253
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_240

theorem link2_241 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 37 w=rows2 w 241 := by
  change jetBlockRow (1) (-1) 3 37 w=((-2662)/3)*w 0 + ((-2662)/3)*w 6 + ((-2662)/3)*w 12 + ((-2662)/3)*w 18 + ((-2662)/3)*w 24 + ((-2662)/3)*w 30 + ((-2662)/3)*w 36 + ((-2662)/3)*w 42 + ((-2662)/3)*w 48 + ((-2662)/3)*w 54 + ((-242))*w 66 + ((-242))*w 72 + ((-242))*w 78 + ((-242))*w 84 + ((-242))*w 90 + ((-242))*w 96 + ((-242))*w 102 + ((-242))*w 108 + ((-242))*w 114 + ((-242))*w 120 + ((-44))*w 132 + ((-44))*w 138 + ((-44))*w 144 + ((-44))*w 150 + ((-44))*w 156 + ((-44))*w 162 + ((-44))*w 168 + ((-44))*w 174 + ((-44))*w 180 + ((-44))*w 186 + ((-4))*w 198 + ((-4))*w 204 + (1)*w 207 + ((-4))*w 210 + (1)*w 213 + ((-4))*w 216 + (1)*w 219 + ((-4))*w 222 + (1)*w 225 + ((-4))*w 228 + (1)*w 231 + ((-4))*w 234 + (1)*w 237 + ((-4))*w 240 + (1)*w 243 + ((-4))*w 246 + (1)*w 249 + ((-4))*w 252 + (1)*w 255 + (1)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_241

theorem link2_242 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 38 w=rows2 w 242 := by
  change jetBlockRow (1) (-1) 3 38 w=(4356)*w 0 + (4356)*w 22 + ((-2178))*w 66 + ((-2178))*w 88 + (726)*w 132 + (726)*w 154 + ((-121))*w 198 + (1)*w 208 + ((-121))*w 220 + (1)*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_242

theorem link2_243 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 39 w=rows2 w 243 := by
  change jetBlockRow (1) (-1) 3 39 w=((-4356))*w 0 + ((-4356))*w 44 + ((-2178))*w 66 + ((-2178))*w 110 + ((-726))*w 132 + ((-726))*w 176 + ((-121))*w 198 + (1)*w 210 + ((-121))*w 242 + (1)*w 254
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_243

theorem link2_244 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 40 w=rows2 w 244 := by
  change jetBlockRow (1) (-1) 3 40 w=((-2178))*w 0 + ((-2178))*w 22 + ((-2178))*w 66 + ((-2178))*w 88 + ((-1452))*w 132 + ((-1452))*w 154 + ((-484))*w 198 + ((-484))*w 220 + (1)*w 221 + (1)*w 243
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_244

theorem link2_245 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 41 w=rows2 w 245 := by
  change jetBlockRow (1) (-1) 3 41 w=(2178)*w 0 + (2178)*w 44 + ((-2178))*w 66 + ((-2178))*w 110 + (1452)*w 132 + (1452)*w 176 + ((-484))*w 198 + (1)*w 219 + (1)*w 241 + ((-484))*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_245

theorem link2_246 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 42 w=rows2 w 246 := by
  change jetBlockRow (1) (-1) 3 42 w=((-2662))*w 0 + ((-2662))*w 6 + ((-2662))*w 12 + ((-2662))*w 18 + ((-2662))*w 24 + ((-2662))*w 30 + ((-2662))*w 36 + ((-2662))*w 42 + ((-2662))*w 54 + ((-2662))*w 60 + ((-2178))*w 66 + ((-2178))*w 72 + ((-2178))*w 78 + ((-2178))*w 84 + ((-2178))*w 90 + ((-2178))*w 96 + ((-2178))*w 102 + ((-2178))*w 108 + ((-2178))*w 120 + ((-2178))*w 126 + ((-1188))*w 132 + ((-1188))*w 138 + ((-1188))*w 144 + ((-1188))*w 150 + ((-1188))*w 156 + ((-1188))*w 162 + ((-1188))*w 168 + ((-1188))*w 174 + ((-1188))*w 186 + ((-1188))*w 192 + ((-324))*w 198 + ((-324))*w 204 + (1)*w 205 + ((-324))*w 210 + (1)*w 211 + ((-324))*w 216 + (1)*w 217 + ((-324))*w 222 + (1)*w 223 + ((-324))*w 228 + (1)*w 229 + ((-324))*w 234 + (1)*w 235 + ((-324))*w 240 + (1)*w 241 + (1)*w 247 + ((-324))*w 252 + (1)*w 253 + ((-324))*w 258 + (1)*w 259
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_246

theorem link2_247 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 43 w=rows2 w 247 := by
  change jetBlockRow (1) (-1) 3 43 w=(1331)*w 3 + (1331)*w 15 + (1331)*w 21 + (1331)*w 27 + (1331)*w 33 + (1331)*w 39 + (1331)*w 45 + (1331)*w 51 + (1331)*w 57 + (1331)*w 63 + ((-1089)/2)*w 69 + ((-1089)/2)*w 81 + ((-1089)/2)*w 87 + ((-1089)/2)*w 93 + ((-1089)/2)*w 99 + ((-1089)/2)*w 105 + ((-1089)/2)*w 111 + ((-1089)/2)*w 117 + ((-1089)/2)*w 123 + ((-1089)/2)*w 129 + (297/2)*w 135 + (297/2)*w 147 + (297/2)*w 153 + (297/2)*w 159 + (297/2)*w 165 + (297/2)*w 171 + (297/2)*w 177 + (297/2)*w 183 + (297/2)*w 189 + (297/2)*w 195 + ((-81)/4)*w 201 + (1)*w 202 + (1)*w 208 + ((-81)/4)*w 213 + (1)*w 214 + ((-81)/4)*w 219 + (1)*w 220 + ((-81)/4)*w 225 + (1)*w 226 + ((-81)/4)*w 231 + (1)*w 232 + ((-81)/4)*w 237 + (1)*w 238 + ((-81)/4)*w 243 + (1)*w 244 + ((-81)/4)*w 249 + (1)*w 250 + ((-81)/4)*w 255 + (1)*w 256 + ((-81)/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_247

theorem link2_248 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 44 w=rows2 w 248 := by
  change jetBlockRow (1) (-1) 3 44 w=((-1331))*w 3 + ((-1331))*w 9 + ((-1331))*w 15 + ((-1331))*w 21 + ((-1331))*w 27 + ((-1331))*w 33 + ((-1331))*w 39 + ((-1331))*w 45 + ((-1331))*w 51 + ((-1331))*w 63 + ((-1089)/2)*w 69 + ((-1089)/2)*w 75 + ((-1089)/2)*w 81 + ((-1089)/2)*w 87 + ((-1089)/2)*w 93 + ((-1089)/2)*w 99 + ((-1089)/2)*w 105 + ((-1089)/2)*w 111 + ((-1089)/2)*w 117 + ((-1089)/2)*w 129 + ((-297)/2)*w 135 + ((-297)/2)*w 141 + ((-297)/2)*w 147 + ((-297)/2)*w 153 + ((-297)/2)*w 159 + ((-297)/2)*w 165 + ((-297)/2)*w 171 + ((-297)/2)*w 177 + ((-297)/2)*w 183 + ((-297)/2)*w 195 + ((-81)/4)*w 201 + (1)*w 206 + ((-81)/4)*w 207 + (1)*w 212 + ((-81)/4)*w 213 + (1)*w 218 + ((-81)/4)*w 219 + (1)*w 224 + ((-81)/4)*w 225 + (1)*w 230 + ((-81)/4)*w 231 + (1)*w 236 + ((-81)/4)*w 237 + (1)*w 242 + ((-81)/4)*w 243 + (1)*w 248 + ((-81)/4)*w 249 + (1)*w 254 + (1)*w 260 + ((-81)/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_248

theorem link2_249 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 45 w=rows2 w 249 := by
  change jetBlockRow (1) (-1) 3 45 w=(2662)*w 0 + (2662)*w 6 + (2662)*w 12 + (2662)*w 24 + (2662)*w 30 + (2662)*w 36 + (2662)*w 42 + (2662)*w 48 + (2662)*w 54 + (2662)*w 60 + ((-2178))*w 66 + ((-2178))*w 72 + ((-2178))*w 78 + ((-2178))*w 90 + ((-2178))*w 96 + ((-2178))*w 102 + ((-2178))*w 108 + ((-2178))*w 114 + ((-2178))*w 120 + ((-2178))*w 126 + (1188)*w 132 + (1188)*w 138 + (1188)*w 144 + (1188)*w 156 + (1188)*w 162 + (1188)*w 168 + (1188)*w 174 + (1188)*w 180 + (1188)*w 186 + (1188)*w 192 + ((-324))*w 198 + (1)*w 203 + ((-324))*w 204 + (1)*w 209 + ((-324))*w 210 + (1)*w 215 + (1)*w 221 + ((-324))*w 222 + (1)*w 227 + ((-324))*w 228 + (1)*w 233 + ((-324))*w 234 + (1)*w 239 + ((-324))*w 240 + (1)*w 245 + ((-324))*w 246 + (1)*w 251 + ((-324))*w 252 + (1)*w 257 + ((-324))*w 258
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_249

theorem link2_250 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 46 w=rows2 w 250 := by
  change jetBlockRow (1) (-1) 3 46 w=(1)*w 198
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_250

theorem link2_251 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 47 w=rows2 w 251 := by
  change jetBlockRow (1) (-1) 3 47 w=(1)*w 220 + (1)*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_251

theorem link2_252 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 48 w=rows2 w 252 := by
  change jetBlockRow (1) (-1) 3 48 w=(1)*w 209 + (1)*w 253
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_252

theorem link2_253 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 49 w=rows2 w 253 := by
  change jetBlockRow (1) (-1) 3 49 w=(1)*w 204 + (1)*w 210 + (1)*w 216 + (1)*w 222 + (1)*w 228 + (1)*w 234 + (1)*w 240 + (1)*w 246 + (1)*w 252 + (1)*w 258
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_253

theorem link2_254 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 50 w=rows2 w 254 := by
  change jetBlockRow (1) (-1) 3 50 w=(1)*w 207 + (4)*w 216 + (1)*w 240
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_254

theorem link2_255 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 51 w=rows2 w 255 := by
  change jetBlockRow (1) (-1) 3 51 w=(1)*w 213 + (4)*w 228 + (1)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_255

theorem link2_256 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 52 w=rows2 w 256 := by
  change jetBlockRow (1) (-1) 3 52 w=(1)*w 214 + (4)*w 230 + (1)*w 247
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_256

theorem link2_257 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 53 w=rows2 w 257 := by
  change jetBlockRow (1) (-1) 3 53 w=(1)*w 215 + (4)*w 232 + (1)*w 248
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_257

theorem link2_258 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 54 w=rows2 w 258 := by
  change jetBlockRow (1) (-1) 3 54 w=(1)*w 216 + (4)*w 234 + (1)*w 249
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_258

theorem link2_259 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 55 w=rows2 w 259 := by
  change jetBlockRow (1) (-1) 3 55 w=(1)*w 203 + (4)*w 208 + (1)*w 236
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_259

theorem link2_260 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 56 w=rows2 w 260 := by
  change jetBlockRow (1) (-1) 3 56 w=(1)*w 202 + (4)*w 206 + (1)*w 235
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_260

theorem link2_261 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 57 w=rows2 w 261 := by
  change jetBlockRow (1) (-1) 3 57 w=(1)*w 205 + (21)*w 219 + (1)*w 227 + (1)*w 249 + (81)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_261

theorem link2_262 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 58 w=rows2 w 262 := by
  change jetBlockRow (1) (-1) 3 58 w=(1)*w 202 + (21)*w 210 + (1)*w 224 + (81)*w 234 + (1)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_262

theorem link2_263 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 59 w=rows2 w 263 := by
  change jetBlockRow (1) (-1) 3 59 w=(1)*w 211 + (4)*w 224 + (1)*w 244
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_263

theorem link2_264 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 60 w=rows2 w 264 := by
  change jetBlockRow (1) (-1) 3 60 w=(1)*w 224 + (4)*w 250 + (1)*w 257
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_264

theorem link2_265 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 61 w=rows2 w 265 := by
  change jetBlockRow (1) (-1) 3 61 w=(1)*w 217 + (4)*w 236 + (1)*w 250
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_265

theorem link2_266 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 62 w=rows2 w 266 := by
  change jetBlockRow (1) (-1) 3 62 w=(1)*w 203 + (21)*w 213 + (1)*w 225 + (81)*w 243 + (1)*w 247
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_266

theorem link2_267 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 63 w=rows2 w 267 := by
  change jetBlockRow (1) (-1) 3 63 w=(1)*w 205 + (4)*w 212 + (1)*w 238
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_267

theorem link2_268 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 64 w=rows2 w 268 := by
  change jetBlockRow (1) (-1) 3 64 w=(1)*w 206 + (4)*w 214 + (1)*w 239
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_268

theorem link2_269 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 65 w=rows2 w 269 := by
  change jetBlockRow (1) (-1) 3 65 w=(1)*w 212 + (4)*w 226 + (1)*w 245
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_269

theorem link2_270 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 66 w=rows2 w 270 := by
  change jetBlockRow (1) (-1) 3 66 w=(1)*w 204 + (4)*w 210 + (1)*w 237
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_270

theorem link2_271 (w : Fin 264→ℂ) : jetBlockRow (1) (-1) 3 67 w=rows2 w 271 := by
  change jetBlockRow (1) (-1) 3 67 w=(1)*w 226 + (4)*w 254 + (1)*w 259
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link2_271

end SmallLevelTwentyTwoJetBlock
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoJetBlock
open Complex SmallLevelFiniteShift SmallLevelTwentyTwoLaurent SmallLevelTwentyTwoThirdJet

theorem link3_0 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 0 w=rows3 w 0 := by
  change jetBlockRow (1) (1) 0 0 w=(1)*w 0 + ((-22))*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_0

theorem link3_1 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 1 w=rows3 w 1 := by
  change jetBlockRow (1) (1) 0 1 w=((-1)/198)*w 0 + (1)*w 1
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_1

theorem link3_2 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 2 w=rows3 w 2 := by
  change jetBlockRow (1) (1) 0 2 w=((-1)/22)*w 0 + (1)*w 3
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_2

theorem link3_3 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 3 w=rows3 w 3 := by
  change jetBlockRow (1) (1) 0 3 w=((-1)/198)*w 0 + (1)*w 65
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_3

theorem link3_4 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 4 w=rows3 w 4 := by
  change jetBlockRow (1) (1) 0 4 w=(1)*w 30 + ((-18))*w 65
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_4

theorem link3_5 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 5 w=rows3 w 5 := by
  change jetBlockRow (1) (1) 0 5 w=((-1)/2)*w 0 + (1)*w 33
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_5

theorem link3_6 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 6 w=rows3 w 6 := by
  change jetBlockRow (1) (1) 0 6 w=(1)*w 33 + ((-99)/2)*w 64
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_6

theorem link3_7 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 7 w=rows3 w 7 := by
  change jetBlockRow (1) (1) 0 7 w=(1)*w 2 + ((-2)/99)*w 33
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_7

theorem link3_8 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 8 w=rows3 w 8 := by
  change jetBlockRow (1) (1) 0 8 w=(1)*w 6 + ((-2)/11)*w 33
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_8

theorem link3_9 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 9 w=rows3 w 9 := by
  change jetBlockRow (1) (1) 0 9 w=(1)*w 33 + ((-11)/2)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_9

theorem link3_10 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 10 w=rows3 w 10 := by
  change jetBlockRow (1) (1) 0 10 w=(1)*w 34 + ((-2)/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_10

theorem link3_11 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 11 w=rows3 w 11 := by
  change jetBlockRow (1) (1) 0 11 w=(1)*w 32 + ((-2))*w 65
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_11

theorem link3_12 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 12 w=rows3 w 12 := by
  change jetBlockRow (1) (1) 0 12 w=(1)*w 36 + ((-2))*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_12

theorem link3_13 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 13 w=rows3 w 13 := by
  change jetBlockRow (1) (1) 0 13 w=(1)*w 9 + ((-9)/22)*w 44
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_13

theorem link3_14 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 14 w=rows3 w 14 := by
  change jetBlockRow (1) (1) 0 14 w=(1)*w 11 + ((-11)/18)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_14

theorem link3_15 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 15 w=rows3 w 15 := by
  change jetBlockRow (1) (1) 0 15 w=(1)*w 18 + ((-18)/11)*w 55
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_15

theorem link3_16 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 16 w=rows3 w 16 := by
  change jetBlockRow (1) (1) 0 16 w=(1)*w 22 + ((-22)/9)*w 57
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_16

theorem link3_17 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 17 w=rows3 w 17 := by
  change jetBlockRow (1) (1) 0 17 w=((-9))*w 4 + (1)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_17

theorem link3_18 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 18 w=rows3 w 18 := by
  change jetBlockRow (1) (1) 0 18 w=((-1)/9)*w 12 + (1)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_18

theorem link3_19 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 19 w=rows3 w 19 := by
  change jetBlockRow (1) (1) 0 19 w=(1)*w 35 + ((-1)/2)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_19

theorem link3_20 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 20 w=rows3 w 20 := by
  change jetBlockRow (1) (1) 0 20 w=(1)*w 18 + ((-18))*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_20

theorem link3_21 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 21 w=rows3 w 21 := by
  change jetBlockRow (1) (1) 0 21 w=(1)*w 27 + ((-9)/2)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_21

theorem link3_22 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 22 w=rows3 w 22 := by
  change jetBlockRow (1) (1) 0 22 w=(1)*w 37 + ((-1)/18)*w 42
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_22

theorem link3_23 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 23 w=rows3 w 23 := by
  change jetBlockRow (1) (1) 0 23 w=(1)*w 38 + ((-2)/9)*w 51
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_23

theorem link3_24 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 24 w=rows3 w 24 := by
  change jetBlockRow (1) (1) 0 24 w=(1)*w 39 + ((-1)/2)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_24

theorem link3_25 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 25 w=rows3 w 25 := by
  change jetBlockRow (1) (1) 0 25 w=(1)*w 42 + ((-2))*w 57
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_25

theorem link3_26 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 26 w=rows3 w 26 := by
  change jetBlockRow (1) (1) 0 26 w=(1)*w 45 + ((-9)/2)*w 58
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_26

theorem link3_27 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 27 w=rows3 w 27 := by
  change jetBlockRow (1) (1) 0 27 w=(1)*w 54 + ((-18))*w 59
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_27

theorem link3_28 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 28 w=rows3 w 28 := by
  change jetBlockRow (1) (1) 0 28 w=((-18))*w 7 + (1)*w 12
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_28

theorem link3_29 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 29 w=rows3 w 29 := by
  change jetBlockRow (1) (1) 0 29 w=((-9)/2)*w 8 + (1)*w 21
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_29

theorem link3_30 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 30 w=rows3 w 30 := by
  change jetBlockRow (1) (1) 0 30 w=((-2))*w 9 + (1)*w 24
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_30

theorem link3_31 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 31 w=rows3 w 31 := by
  change jetBlockRow (1) (1) 0 31 w=((-2)/9)*w 15 + (1)*w 28
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_31

theorem link3_32 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 32 w=rows3 w 32 := by
  change jetBlockRow (1) (1) 0 32 w=((-1)/18)*w 24 + (1)*w 29
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_32

theorem link3_33 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 33 w=rows3 w 33 := by
  change jetBlockRow (1) (1) 0 33 w=(1)*w 31 + ((-1)/18)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_33

theorem link3_34 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 34 w=rows3 w 34 := by
  change jetBlockRow (1) (1) 0 34 w=((-18))*w 5 + (1)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_34

theorem link3_35 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 35 w=rows3 w 35 := by
  change jetBlockRow (1) (1) 0 35 w=((-2)/11)*w 11 + (1)*w 24 + ((-2)/11)*w 33 + (1)*w 46
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_35

theorem link3_36 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 36 w=rows3 w 36 := by
  change jetBlockRow (1) (1) 0 36 w=(1)*w 20 + ((-2)/11)*w 33 + (1)*w 42 + ((-2)/11)*w 55
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_36

theorem link3_37 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 37 w=rows3 w 37 := by
  change jetBlockRow (1) (1) 0 37 w=(1/2)*w 0 + (1/2)*w 6 + (1)*w 9 + (1/2)*w 12 + (1)*w 15 + (1/2)*w 18 + (1)*w 21 + (1/2)*w 24 + (1)*w 27 + (1/2)*w 30 + (1)*w 33 + (1/2)*w 36 + (1)*w 39 + (1/2)*w 42 + (1)*w 45 + (1/2)*w 48 + (1)*w 51 + (1/2)*w 54 + (1)*w 57 + (1)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_37

theorem link3_38 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 38 w=rows3 w 38 := by
  change jetBlockRow (1) (1) 0 38 w=((-1)/11)*w 0 + (1)*w 10 + ((-1)/11)*w 22 + (1)*w 54
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_38

theorem link3_39 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 39 w=rows3 w 39 := by
  change jetBlockRow (1) (1) 0 39 w=((-1)/11)*w 0 + (1)*w 12 + ((-1)/11)*w 44 + (1)*w 56
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_39

theorem link3_40 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 40 w=rows3 w 40 := by
  change jetBlockRow (1) (1) 0 40 w=((-1)/22)*w 0 + ((-1)/22)*w 22 + (1)*w 23 + (1)*w 45
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_40

theorem link3_41 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 41 w=rows3 w 41 := by
  change jetBlockRow (1) (1) 0 41 w=((-1)/22)*w 0 + (1)*w 21 + (1)*w 43 + ((-1)/22)*w 44
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_41

theorem link3_42 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 42 w=rows3 w 42 := by
  change jetBlockRow (1) (1) 0 42 w=(1/18)*w 0 + (1/18)*w 6 + (1)*w 7 + (1/18)*w 12 + (1)*w 13 + (1/18)*w 18 + (1)*w 19 + (1/18)*w 24 + (1)*w 25 + (1/18)*w 30 + (1)*w 31 + (1/18)*w 36 + (1)*w 37 + (1/18)*w 42 + (1)*w 43 + (1)*w 49 + (1/18)*w 54 + (1)*w 55 + (1/18)*w 60 + (1)*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_42

theorem link3_43 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 43 w=rows3 w 43 := by
  change jetBlockRow (1) (1) 0 43 w=(2/9)*w 3 + (1)*w 4 + (1)*w 10 + (2/9)*w 15 + (1)*w 16 + (2/9)*w 21 + (1)*w 22 + (2/9)*w 27 + (1)*w 28 + (2/9)*w 33 + (1)*w 34 + (2/9)*w 39 + (1)*w 40 + (2/9)*w 45 + (1)*w 46 + (2/9)*w 51 + (1)*w 52 + (2/9)*w 57 + (1)*w 58 + (2/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_43

theorem link3_44 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 44 w=rows3 w 44 := by
  change jetBlockRow (1) (1) 0 44 w=(2/9)*w 3 + (1)*w 8 + (2/9)*w 9 + (1)*w 14 + (2/9)*w 15 + (1)*w 20 + (2/9)*w 21 + (1)*w 26 + (2/9)*w 27 + (1)*w 32 + (2/9)*w 33 + (1)*w 38 + (2/9)*w 39 + (1)*w 44 + (2/9)*w 45 + (1)*w 50 + (2/9)*w 51 + (1)*w 56 + (1)*w 62 + (2/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_44

theorem link3_45 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 45 w=rows3 w 45 := by
  change jetBlockRow (1) (1) 0 45 w=(1/18)*w 0 + (1)*w 5 + (1/18)*w 6 + (1)*w 11 + (1/18)*w 12 + (1)*w 17 + (1)*w 23 + (1/18)*w 24 + (1)*w 29 + (1/18)*w 30 + (1)*w 35 + (1/18)*w 36 + (1)*w 41 + (1/18)*w 42 + (1)*w 47 + (1/18)*w 48 + (1)*w 53 + (1/18)*w 54 + (1)*w 59 + (1/18)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_45

theorem link3_46 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 46 w=rows3 w 46 := by
  change jetBlockRow (1) (1) 0 46 w=(1)*w 0
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_46

theorem link3_47 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 47 w=rows3 w 47 := by
  change jetBlockRow (1) (1) 0 47 w=(1)*w 22 + (1)*w 44
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_47

theorem link3_48 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 48 w=rows3 w 48 := by
  change jetBlockRow (1) (1) 0 48 w=(1)*w 11 + (1)*w 55
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_48

theorem link3_49 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 49 w=rows3 w 49 := by
  change jetBlockRow (1) (1) 0 49 w=(1)*w 6 + (1)*w 12 + (1)*w 18 + (1)*w 24 + (1)*w 30 + (1)*w 36 + (1)*w 42 + (1)*w 48 + (1)*w 54 + (1)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_49

theorem link3_50 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 50 w=rows3 w 50 := by
  change jetBlockRow (1) (1) 0 50 w=(1)*w 9 + (1/2)*w 18 + (1)*w 42
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_50

theorem link3_51 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 51 w=rows3 w 51 := by
  change jetBlockRow (1) (1) 0 51 w=(1)*w 15 + (1/2)*w 30 + (1)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_51

theorem link3_52 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 52 w=rows3 w 52 := by
  change jetBlockRow (1) (1) 0 52 w=(1)*w 16 + (1/2)*w 32 + (1)*w 49
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_52

theorem link3_53 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 53 w=rows3 w 53 := by
  change jetBlockRow (1) (1) 0 53 w=(1)*w 17 + (1/2)*w 34 + (1)*w 50
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_53

theorem link3_54 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 54 w=rows3 w 54 := by
  change jetBlockRow (1) (1) 0 54 w=(1)*w 18 + (1/2)*w 36 + (1)*w 51
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_54

theorem link3_55 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 55 w=rows3 w 55 := by
  change jetBlockRow (1) (1) 0 55 w=(1)*w 5 + (1/2)*w 10 + (1)*w 38
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_55

theorem link3_56 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 56 w=rows3 w 56 := by
  change jetBlockRow (1) (1) 0 56 w=(1)*w 4 + (1/2)*w 8 + (1)*w 37
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_56

theorem link3_57 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 57 w=rows3 w 57 := by
  change jetBlockRow (1) (1) 0 57 w=(1)*w 7 + (7/9)*w 21 + (1)*w 29 + (1)*w 51 + (1/9)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_57

theorem link3_58 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 58 w=rows3 w 58 := by
  change jetBlockRow (1) (1) 0 58 w=(1)*w 4 + (7/9)*w 12 + (1)*w 26 + (1/9)*w 36 + (1)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_58

theorem link3_59 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 59 w=rows3 w 59 := by
  change jetBlockRow (1) (1) 0 59 w=(1)*w 13 + (1/2)*w 26 + (1)*w 46
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_59

theorem link3_60 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 60 w=rows3 w 60 := by
  change jetBlockRow (1) (1) 0 60 w=(1)*w 26 + (1/2)*w 52 + (1)*w 59
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_60

theorem link3_61 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 61 w=rows3 w 61 := by
  change jetBlockRow (1) (1) 0 61 w=(1)*w 19 + (1/2)*w 38 + (1)*w 52
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_61

theorem link3_62 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 62 w=rows3 w 62 := by
  change jetBlockRow (1) (1) 0 62 w=(1)*w 5 + (7/9)*w 15 + (1)*w 27 + (1/9)*w 45 + (1)*w 49
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_62

theorem link3_63 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 63 w=rows3 w 63 := by
  change jetBlockRow (1) (1) 0 63 w=(1)*w 7 + (1/2)*w 14 + (1)*w 40
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_63

theorem link3_64 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 64 w=rows3 w 64 := by
  change jetBlockRow (1) (1) 0 64 w=(1)*w 8 + (1/2)*w 16 + (1)*w 41
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_64

theorem link3_65 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 65 w=rows3 w 65 := by
  change jetBlockRow (1) (1) 0 65 w=(1)*w 14 + (1/2)*w 28 + (1)*w 47
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_65

theorem link3_66 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 66 w=rows3 w 66 := by
  change jetBlockRow (1) (1) 0 66 w=(1)*w 6 + (1/2)*w 12 + (1)*w 39
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_66

theorem link3_67 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 0 67 w=rows3 w 67 := by
  change jetBlockRow (1) (1) 0 67 w=(1)*w 28 + (1/2)*w 56 + (1)*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_67

theorem link3_68 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 0 w=rows3 w 68 := by
  change jetBlockRow (1) (1) 1 0 w=((-22))*w 63 + (1)*w 66 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_68

theorem link3_69 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 1 w=rows3 w 69 := by
  change jetBlockRow (1) (1) 1 1 w=((-1)/3)*w 0 + ((-1))*w 66 + (1)*w 67
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_69

theorem link3_70 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 2 w=rows3 w 70 := by
  change jetBlockRow (1) (1) 1 2 w=((-1))*w 0 + ((-1))*w 66 + (1)*w 69
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_70

theorem link3_71 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 3 w=rows3 w 71 := by
  change jetBlockRow (1) (1) 1 3 w=(1/3)*w 0 + ((-1))*w 66 + (1)*w 131
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_71

theorem link3_72 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 4 w=rows3 w 72 := by
  change jetBlockRow (1) (1) 1 4 w=(330)*w 65 + (1)*w 96 + ((-1))*w 131
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_72

theorem link3_73 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 5 w=rows3 w 73 := by
  change jetBlockRow (1) (1) 1 5 w=(55)*w 0 + ((-1))*w 66 + (1)*w 99
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_73

theorem link3_74 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 6 w=rows3 w 74 := by
  change jetBlockRow (1) (1) 1 6 w=((-33))*w 64 + (1)*w 99 + ((-1))*w 130
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_74

theorem link3_75 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 7 w=rows3 w 75 := by
  change jetBlockRow (1) (1) 1 7 w=((-2)/3)*w 33 + (1)*w 68 + ((-1))*w 99
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_75

theorem link3_76 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 8 w=rows3 w 76 := by
  change jetBlockRow (1) (1) 1 8 w=((-2))*w 33 + (1)*w 72 + ((-1))*w 99
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_76

theorem link3_77 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 9 w=rows3 w 77 := by
  change jetBlockRow (1) (1) 1 9 w=((-11))*w 60 + (1)*w 99 + ((-1))*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_77

theorem link3_78 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 10 w=rows3 w 78 := by
  change jetBlockRow (1) (1) 1 10 w=((-110)/3)*w 63 + (1)*w 100 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_78

theorem link3_79 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 11 w=rows3 w 79 := by
  change jetBlockRow (1) (1) 1 11 w=(66)*w 65 + (1)*w 98 + ((-1))*w 131
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_79

theorem link3_80 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 12 w=rows3 w 80 := by
  change jetBlockRow (1) (1) 1 12 w=((-66))*w 63 + (1)*w 102 + ((-1))*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_80

theorem link3_81 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 13 w=rows3 w 81 := by
  change jetBlockRow (1) (1) 1 13 w=((-3))*w 44 + (1)*w 75 + ((-1))*w 110
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_81

theorem link3_82 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 14 w=rows3 w 82 := by
  change jetBlockRow (1) (1) 1 14 w=((-11)/3)*w 48 + (1)*w 77 + ((-1))*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_82

theorem link3_83 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 15 w=rows3 w 83 := by
  change jetBlockRow (1) (1) 1 15 w=((-6))*w 55 + (1)*w 84 + ((-1))*w 121
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_83

theorem link3_84 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 16 w=rows3 w 84 := by
  change jetBlockRow (1) (1) 1 16 w=((-22)/3)*w 57 + (1)*w 88 + ((-1))*w 123
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_84

theorem link3_85 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 17 w=rows3 w 85 := by
  change jetBlockRow (1) (1) 1 17 w=(66)*w 4 + ((-1))*w 70 + (1)*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_85

theorem link3_86 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 18 w=rows3 w 86 := by
  change jetBlockRow (1) (1) 1 18 w=(22/3)*w 12 + ((-1))*w 78 + (1)*w 128
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_86

theorem link3_87 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 19 w=rows3 w 87 := by
  change jetBlockRow (1) (1) 1 19 w=((-33))*w 62 + (1)*w 101 + ((-1))*w 128
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_87

theorem link3_88 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 20 w=rows3 w 88 := by
  change jetBlockRow (1) (1) 1 20 w=(66)*w 61 + (1)*w 84 + ((-1))*w 127
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_88

theorem link3_89 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 21 w=rows3 w 89 := by
  change jetBlockRow (1) (1) 1 21 w=(33)*w 62 + (1)*w 93 + ((-1))*w 128
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_89

theorem link3_90 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 22 w=rows3 w 90 := by
  change jetBlockRow (1) (1) 1 22 w=((-11)/3)*w 42 + (1)*w 103 + ((-1))*w 108
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_90

theorem link3_91 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 23 w=rows3 w 91 := by
  change jetBlockRow (1) (1) 1 23 w=((-22)/3)*w 51 + (1)*w 104 + ((-1))*w 117
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_91

theorem link3_92 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 24 w=rows3 w 92 := by
  change jetBlockRow (1) (1) 1 24 w=((-11))*w 54 + (1)*w 105 + ((-1))*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_92

theorem link3_93 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 25 w=rows3 w 93 := by
  change jetBlockRow (1) (1) 1 25 w=((-22))*w 57 + (1)*w 108 + ((-1))*w 123
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_93

theorem link3_94 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 26 w=rows3 w 94 := by
  change jetBlockRow (1) (1) 1 26 w=((-33))*w 58 + (1)*w 111 + ((-1))*w 124
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_94

theorem link3_95 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 27 w=rows3 w 95 := by
  change jetBlockRow (1) (1) 1 27 w=((-66))*w 59 + (1)*w 120 + ((-1))*w 125
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_95

theorem link3_96 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 28 w=rows3 w 96 := by
  change jetBlockRow (1) (1) 1 28 w=(66)*w 7 + ((-1))*w 73 + (1)*w 78
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_96

theorem link3_97 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 29 w=rows3 w 97 := by
  change jetBlockRow (1) (1) 1 29 w=(33)*w 8 + ((-1))*w 74 + (1)*w 87
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_97

theorem link3_98 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 30 w=rows3 w 98 := by
  change jetBlockRow (1) (1) 1 30 w=(22)*w 9 + ((-1))*w 75 + (1)*w 90
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_98

theorem link3_99 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 31 w=rows3 w 99 := by
  change jetBlockRow (1) (1) 1 31 w=(22/3)*w 15 + ((-1))*w 81 + (1)*w 94
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_99

theorem link3_100 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 32 w=rows3 w 100 := by
  change jetBlockRow (1) (1) 1 32 w=(11/3)*w 24 + ((-1))*w 90 + (1)*w 95
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_100

theorem link3_101 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 33 w=rows3 w 101 := by
  change jetBlockRow (1) (1) 1 33 w=((-11)/3)*w 54 + (1)*w 97 + ((-1))*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_101

theorem link3_102 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 34 w=rows3 w 102 := by
  change jetBlockRow (1) (1) 1 34 w=((-66))*w 5 + ((-1))*w 71 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_102

theorem link3_103 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 35 w=rows3 w 103 := by
  change jetBlockRow (1) (1) 1 35 w=((-6))*w 11 + ((-6))*w 33 + ((-1))*w 77 + (1)*w 90 + ((-1))*w 99 + (1)*w 112
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_103

theorem link3_104 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 36 w=rows3 w 104 := by
  change jetBlockRow (1) (1) 1 36 w=(6)*w 33 + (6)*w 55 + (1)*w 86 + ((-1))*w 99 + (1)*w 108 + ((-1))*w 121
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_104

theorem link3_105 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 37 w=rows3 w 105 := by
  change jetBlockRow (1) (1) 1 37 w=(11)*w 0 + (11)*w 6 + (11)*w 12 + (11)*w 18 + (11)*w 24 + (11)*w 30 + (11)*w 36 + (11)*w 42 + (11)*w 48 + (11)*w 54 + (1)*w 66 + (1)*w 72 + (1)*w 75 + (1)*w 78 + (1)*w 81 + (1)*w 84 + (1)*w 87 + (1)*w 90 + (1)*w 93 + (1)*w 96 + (1)*w 99 + (1)*w 102 + (1)*w 105 + (1)*w 108 + (1)*w 111 + (1)*w 114 + (1)*w 117 + (1)*w 120 + (1)*w 123 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_105

theorem link3_106 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 38 w=rows3 w 106 := by
  change jetBlockRow (1) (1) 1 38 w=(6)*w 0 + (6)*w 22 + ((-1))*w 66 + (1)*w 76 + ((-1))*w 88 + (1)*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_106

theorem link3_107 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 39 w=rows3 w 107 := by
  change jetBlockRow (1) (1) 1 39 w=((-6))*w 0 + ((-6))*w 44 + ((-1))*w 66 + (1)*w 78 + ((-1))*w 110 + (1)*w 122
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_107

theorem link3_108 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 40 w=rows3 w 108 := by
  change jetBlockRow (1) (1) 1 40 w=((-3))*w 0 + ((-3))*w 22 + ((-1))*w 66 + ((-1))*w 88 + (1)*w 89 + (1)*w 111
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_108

theorem link3_109 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 41 w=rows3 w 109 := by
  change jetBlockRow (1) (1) 1 41 w=(3)*w 0 + (3)*w 44 + ((-1))*w 66 + (1)*w 87 + (1)*w 109 + ((-1))*w 110
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_109

theorem link3_110 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 42 w=rows3 w 110 := by
  change jetBlockRow (1) (1) 1 42 w=(11/3)*w 0 + (11/3)*w 6 + (11/3)*w 12 + (11/3)*w 18 + (11/3)*w 24 + (11/3)*w 30 + (11/3)*w 36 + (11/3)*w 42 + (11/3)*w 54 + (11/3)*w 60 + (1)*w 66 + (1)*w 72 + (1)*w 73 + (1)*w 78 + (1)*w 79 + (1)*w 84 + (1)*w 85 + (1)*w 90 + (1)*w 91 + (1)*w 96 + (1)*w 97 + (1)*w 102 + (1)*w 103 + (1)*w 108 + (1)*w 109 + (1)*w 115 + (1)*w 120 + (1)*w 121 + (1)*w 126 + (1)*w 127
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_110

theorem link3_111 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 43 w=rows3 w 111 := by
  change jetBlockRow (1) (1) 1 43 w=((-22)/3)*w 3 + ((-22)/3)*w 15 + ((-22)/3)*w 21 + ((-22)/3)*w 27 + ((-22)/3)*w 33 + ((-22)/3)*w 39 + ((-22)/3)*w 45 + ((-22)/3)*w 51 + ((-22)/3)*w 57 + ((-22)/3)*w 63 + (1)*w 69 + (1)*w 70 + (1)*w 76 + (1)*w 81 + (1)*w 82 + (1)*w 87 + (1)*w 88 + (1)*w 93 + (1)*w 94 + (1)*w 99 + (1)*w 100 + (1)*w 105 + (1)*w 106 + (1)*w 111 + (1)*w 112 + (1)*w 117 + (1)*w 118 + (1)*w 123 + (1)*w 124 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_111

theorem link3_112 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 44 w=rows3 w 112 := by
  change jetBlockRow (1) (1) 1 44 w=(22/3)*w 3 + (22/3)*w 9 + (22/3)*w 15 + (22/3)*w 21 + (22/3)*w 27 + (22/3)*w 33 + (22/3)*w 39 + (22/3)*w 45 + (22/3)*w 51 + (22/3)*w 63 + (1)*w 69 + (1)*w 74 + (1)*w 75 + (1)*w 80 + (1)*w 81 + (1)*w 86 + (1)*w 87 + (1)*w 92 + (1)*w 93 + (1)*w 98 + (1)*w 99 + (1)*w 104 + (1)*w 105 + (1)*w 110 + (1)*w 111 + (1)*w 116 + (1)*w 117 + (1)*w 122 + (1)*w 128 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_112

theorem link3_113 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 45 w=rows3 w 113 := by
  change jetBlockRow (1) (1) 1 45 w=((-11)/3)*w 0 + ((-11)/3)*w 6 + ((-11)/3)*w 12 + ((-11)/3)*w 24 + ((-11)/3)*w 30 + ((-11)/3)*w 36 + ((-11)/3)*w 42 + ((-11)/3)*w 48 + ((-11)/3)*w 54 + ((-11)/3)*w 60 + (1)*w 66 + (1)*w 71 + (1)*w 72 + (1)*w 77 + (1)*w 78 + (1)*w 83 + (1)*w 89 + (1)*w 90 + (1)*w 95 + (1)*w 96 + (1)*w 101 + (1)*w 102 + (1)*w 107 + (1)*w 108 + (1)*w 113 + (1)*w 114 + (1)*w 119 + (1)*w 120 + (1)*w 125 + (1)*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_113

theorem link3_114 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 46 w=rows3 w 114 := by
  change jetBlockRow (1) (1) 1 46 w=(1)*w 66
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_114

theorem link3_115 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 47 w=rows3 w 115 := by
  change jetBlockRow (1) (1) 1 47 w=(1)*w 88 + (1)*w 110
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_115

theorem link3_116 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 48 w=rows3 w 116 := by
  change jetBlockRow (1) (1) 1 48 w=(1)*w 77 + (1)*w 121
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_116

theorem link3_117 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 49 w=rows3 w 117 := by
  change jetBlockRow (1) (1) 1 49 w=(1)*w 72 + (1)*w 78 + (1)*w 84 + (1)*w 90 + (1)*w 96 + (1)*w 102 + (1)*w 108 + (1)*w 114 + (1)*w 120 + (1)*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_117

theorem link3_118 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 50 w=rows3 w 118 := by
  change jetBlockRow (1) (1) 1 50 w=(1)*w 75 + (1)*w 84 + (1)*w 108
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_118

theorem link3_119 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 51 w=rows3 w 119 := by
  change jetBlockRow (1) (1) 1 51 w=(1)*w 81 + (1)*w 96 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_119

theorem link3_120 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 52 w=rows3 w 120 := by
  change jetBlockRow (1) (1) 1 52 w=(1)*w 82 + (1)*w 98 + (1)*w 115
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_120

theorem link3_121 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 53 w=rows3 w 121 := by
  change jetBlockRow (1) (1) 1 53 w=(1)*w 83 + (1)*w 100 + (1)*w 116
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_121

theorem link3_122 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 54 w=rows3 w 122 := by
  change jetBlockRow (1) (1) 1 54 w=(1)*w 84 + (1)*w 102 + (1)*w 117
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_122

theorem link3_123 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 55 w=rows3 w 123 := by
  change jetBlockRow (1) (1) 1 55 w=(1)*w 71 + (1)*w 76 + (1)*w 104
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_123

theorem link3_124 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 56 w=rows3 w 124 := by
  change jetBlockRow (1) (1) 1 56 w=(1)*w 70 + (1)*w 74 + (1)*w 103
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_124

theorem link3_125 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 57 w=rows3 w 125 := by
  change jetBlockRow (1) (1) 1 57 w=(1)*w 73 + (7/3)*w 87 + (1)*w 95 + (1)*w 117 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_125

theorem link3_126 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 58 w=rows3 w 126 := by
  change jetBlockRow (1) (1) 1 58 w=(1)*w 70 + (7/3)*w 78 + (1)*w 92 + (1)*w 102 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_126

theorem link3_127 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 59 w=rows3 w 127 := by
  change jetBlockRow (1) (1) 1 59 w=(1)*w 79 + (1)*w 92 + (1)*w 112
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_127

theorem link3_128 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 60 w=rows3 w 128 := by
  change jetBlockRow (1) (1) 1 60 w=(1)*w 92 + (1)*w 118 + (1)*w 125
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_128

theorem link3_129 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 61 w=rows3 w 129 := by
  change jetBlockRow (1) (1) 1 61 w=(1)*w 85 + (1)*w 104 + (1)*w 118
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_129

theorem link3_130 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 62 w=rows3 w 130 := by
  change jetBlockRow (1) (1) 1 62 w=(1)*w 71 + (7/3)*w 81 + (1)*w 93 + (1)*w 111 + (1)*w 115
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_130

theorem link3_131 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 63 w=rows3 w 131 := by
  change jetBlockRow (1) (1) 1 63 w=(1)*w 73 + (1)*w 80 + (1)*w 106
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_131

theorem link3_132 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 64 w=rows3 w 132 := by
  change jetBlockRow (1) (1) 1 64 w=(1)*w 74 + (1)*w 82 + (1)*w 107
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_132

theorem link3_133 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 65 w=rows3 w 133 := by
  change jetBlockRow (1) (1) 1 65 w=(1)*w 80 + (1)*w 94 + (1)*w 113
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_133

theorem link3_134 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 66 w=rows3 w 134 := by
  change jetBlockRow (1) (1) 1 66 w=(1)*w 72 + (1)*w 78 + (1)*w 105
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_134

theorem link3_135 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 1 67 w=rows3 w 135 := by
  change jetBlockRow (1) (1) 1 67 w=(1)*w 94 + (1)*w 122 + (1)*w 127
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_135

theorem link3_136 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 0 w=rows3 w 136 := by
  change jetBlockRow (1) (1) 2 0 w=((-11))*w 63 + ((-1))*w 129 + (1)*w 132 + ((-1)/22)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_136

theorem link3_137 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 1 w=rows3 w 137 := by
  change jetBlockRow (1) (1) 2 1 w=((-11))*w 0 + ((-66))*w 66 + ((-198))*w 132 + (1)*w 133
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_137

theorem link3_138 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 2 w=rows3 w 138 := by
  change jetBlockRow (1) (1) 2 2 w=((-11))*w 0 + ((-22))*w 66 + ((-22))*w 132 + (1)*w 135
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_138

theorem link3_139 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 3 w=rows3 w 139 := by
  change jetBlockRow (1) (1) 2 3 w=((-11))*w 0 + (66)*w 66 + ((-198))*w 132 + (1)*w 197
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_139

theorem link3_140 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 4 w=rows3 w 140 := by
  change jetBlockRow (1) (1) 2 4 w=((-3025))*w 65 + (55/3)*w 131 + (1)*w 162 + ((-1)/18)*w 197
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_140

theorem link3_141 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 5 w=rows3 w 141 := by
  change jetBlockRow (1) (1) 2 5 w=((-3025))*w 0 + (110)*w 66 + ((-2))*w 132 + (1)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_141

theorem link3_142 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 6 w=rows3 w 142 := by
  change jetBlockRow (1) (1) 2 6 w=((-11))*w 64 + ((-2)/3)*w 130 + (1)*w 165 + ((-2)/99)*w 196
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_142

theorem link3_143 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 7 w=rows3 w 143 := by
  change jetBlockRow (1) (1) 2 7 w=((-11))*w 33 + ((-33))*w 99 + (1)*w 134 + ((-99)/2)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_143

theorem link3_144 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 8 w=rows3 w 144 := by
  change jetBlockRow (1) (1) 2 8 w=((-11))*w 33 + ((-11))*w 99 + (1)*w 138 + ((-11)/2)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_144

theorem link3_145 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 9 w=rows3 w 145 := by
  change jetBlockRow (1) (1) 2 9 w=((-11))*w 60 + ((-2))*w 126 + (1)*w 165 + ((-2)/11)*w 192
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_145

theorem link3_146 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 10 w=rows3 w 146 := by
  change jetBlockRow (1) (1) 2 10 w=((-3025))*w 63 + ((-165))*w 129 + (1)*w 166 + ((-9)/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_146

theorem link3_147 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 11 w=rows3 w 147 := by
  change jetBlockRow (1) (1) 2 11 w=((-1089))*w 65 + (33)*w 131 + (1)*w 164 + ((-1)/2)*w 197
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_147

theorem link3_148 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 12 w=rows3 w 148 := by
  change jetBlockRow (1) (1) 2 12 w=((-1089))*w 63 + ((-33))*w 129 + (1)*w 168 + ((-1)/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_148

theorem link3_149 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 13 w=rows3 w 149 := by
  change jetBlockRow (1) (1) 2 13 w=((-11))*w 44 + ((-22)/3)*w 110 + (1)*w 141 + ((-22)/9)*w 176
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_149

theorem link3_150 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 14 w=rows3 w 150 := by
  change jetBlockRow (1) (1) 2 14 w=((-11))*w 48 + ((-6))*w 114 + (1)*w 143 + ((-18)/11)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_150

theorem link3_151 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 15 w=rows3 w 151 := by
  change jetBlockRow (1) (1) 2 15 w=((-11))*w 55 + ((-11)/3)*w 121 + (1)*w 150 + ((-11)/18)*w 187
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_151

theorem link3_152 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 16 w=rows3 w 152 := by
  change jetBlockRow (1) (1) 2 16 w=((-11))*w 57 + ((-3))*w 123 + (1)*w 154 + ((-9)/22)*w 189
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_152

theorem link3_153 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 17 w=rows3 w 153 := by
  change jetBlockRow (1) (1) 2 17 w=((-242))*w 4 + (22/3)*w 70 + ((-1)/9)*w 136 + (1)*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_153

theorem link3_154 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 18 w=rows3 w 154 := by
  change jetBlockRow (1) (1) 2 18 w=((-242))*w 12 + (66)*w 78 + ((-9))*w 144 + (1)*w 194
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_154

theorem link3_155 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 19 w=rows3 w 155 := by
  change jetBlockRow (1) (1) 2 19 w=((-1089))*w 62 + ((-66))*w 128 + (1)*w 167 + ((-2))*w 194
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_155

theorem link3_156 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 20 w=rows3 w 156 := by
  change jetBlockRow (1) (1) 2 20 w=((-121))*w 61 + (11/3)*w 127 + (1)*w 150 + ((-1)/18)*w 193
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_156

theorem link3_157 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 21 w=rows3 w 157 := by
  change jetBlockRow (1) (1) 2 21 w=((-121))*w 62 + (22/3)*w 128 + (1)*w 159 + ((-2)/9)*w 194
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_157

theorem link3_158 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 22 w=rows3 w 158 := by
  change jetBlockRow (1) (1) 2 22 w=((-121))*w 42 + ((-66))*w 108 + (1)*w 169 + ((-18))*w 174
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_158

theorem link3_159 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 23 w=rows3 w 159 := by
  change jetBlockRow (1) (1) 2 23 w=((-121))*w 51 + ((-33))*w 117 + (1)*w 170 + ((-9)/2)*w 183
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_159

theorem link3_160 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 24 w=rows3 w 160 := by
  change jetBlockRow (1) (1) 2 24 w=((-121))*w 54 + ((-22))*w 120 + (1)*w 171 + ((-2))*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_160

theorem link3_161 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 25 w=rows3 w 161 := by
  change jetBlockRow (1) (1) 2 25 w=((-121))*w 57 + ((-11))*w 123 + (1)*w 174 + ((-1)/2)*w 189
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_161

theorem link3_162 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 26 w=rows3 w 162 := by
  change jetBlockRow (1) (1) 2 26 w=((-121))*w 58 + ((-22)/3)*w 124 + (1)*w 177 + ((-2)/9)*w 190
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_162

theorem link3_163 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 27 w=rows3 w 163 := by
  change jetBlockRow (1) (1) 2 27 w=((-121))*w 59 + ((-11)/3)*w 125 + (1)*w 186 + ((-1)/18)*w 191
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_163

theorem link3_164 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 28 w=rows3 w 164 := by
  change jetBlockRow (1) (1) 2 28 w=((-121))*w 7 + (11/3)*w 73 + ((-1)/18)*w 139 + (1)*w 144
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_164

theorem link3_165 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 29 w=rows3 w 165 := by
  change jetBlockRow (1) (1) 2 29 w=((-121))*w 8 + (22/3)*w 74 + ((-2)/9)*w 140 + (1)*w 153
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_165

theorem link3_166 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 30 w=rows3 w 166 := by
  change jetBlockRow (1) (1) 2 30 w=((-121))*w 9 + (11)*w 75 + ((-1)/2)*w 141 + (1)*w 156
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_166

theorem link3_167 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 31 w=rows3 w 167 := by
  change jetBlockRow (1) (1) 2 31 w=((-121))*w 15 + (33)*w 81 + ((-9)/2)*w 147 + (1)*w 160
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_167

theorem link3_168 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 32 w=rows3 w 168 := by
  change jetBlockRow (1) (1) 2 32 w=((-121))*w 24 + (66)*w 90 + ((-18))*w 156 + (1)*w 161
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_168

theorem link3_169 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 33 w=rows3 w 169 := by
  change jetBlockRow (1) (1) 2 33 w=((-121))*w 54 + ((-66))*w 120 + (1)*w 163 + ((-18))*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_169

theorem link3_170 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 34 w=rows3 w 170 := by
  change jetBlockRow (1) (1) 2 34 w=((-121))*w 5 + ((-11)/3)*w 71 + ((-1)/18)*w 137 + (1)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_170

theorem link3_171 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 35 w=rows3 w 171 := by
  change jetBlockRow (1) (1) 2 35 w=((-99))*w 11 + ((-99))*w 33 + ((-33))*w 77 + ((-33))*w 99 + ((-11)/2)*w 143 + (1)*w 156 + ((-11)/2)*w 165 + (1)*w 178
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_171

theorem link3_172 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 36 w=rows3 w 172 := by
  change jetBlockRow (1) (1) 2 36 w=((-99))*w 33 + ((-99))*w 55 + (33)*w 99 + (33)*w 121 + (1)*w 152 + ((-11)/2)*w 165 + (1)*w 174 + ((-11)/2)*w 187
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_172

theorem link3_173 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 37 w=rows3 w 173 := by
  change jetBlockRow (1) (1) 2 37 w=(121)*w 0 + (121)*w 6 + (121)*w 12 + (121)*w 18 + (121)*w 24 + (121)*w 30 + (121)*w 36 + (121)*w 42 + (121)*w 48 + (121)*w 54 + (22)*w 66 + (22)*w 72 + (22)*w 78 + (22)*w 84 + (22)*w 90 + (22)*w 96 + (22)*w 102 + (22)*w 108 + (22)*w 114 + (22)*w 120 + (2)*w 132 + (2)*w 138 + (1)*w 141 + (2)*w 144 + (1)*w 147 + (2)*w 150 + (1)*w 153 + (2)*w 156 + (1)*w 159 + (2)*w 162 + (1)*w 165 + (2)*w 168 + (1)*w 171 + (2)*w 174 + (1)*w 177 + (2)*w 180 + (1)*w 183 + (2)*w 186 + (1)*w 189 + (1)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_173

theorem link3_174 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 38 w=rows3 w 174 := by
  change jetBlockRow (1) (1) 2 38 w=((-198))*w 0 + ((-198))*w 22 + (66)*w 66 + (66)*w 88 + ((-11))*w 132 + (1)*w 142 + ((-11))*w 154 + (1)*w 186
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_174

theorem link3_175 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 39 w=rows3 w 175 := by
  change jetBlockRow (1) (1) 2 39 w=((-198))*w 0 + ((-198))*w 44 + ((-66))*w 66 + ((-66))*w 110 + ((-11))*w 132 + (1)*w 144 + ((-11))*w 176 + (1)*w 188
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_175

theorem link3_176 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 40 w=rows3 w 176 := by
  change jetBlockRow (1) (1) 2 40 w=((-99))*w 0 + ((-99))*w 22 + ((-66))*w 66 + ((-66))*w 88 + ((-22))*w 132 + ((-22))*w 154 + (1)*w 155 + (1)*w 177
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_176

theorem link3_177 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 41 w=rows3 w 177 := by
  change jetBlockRow (1) (1) 2 41 w=((-99))*w 0 + ((-99))*w 44 + (66)*w 66 + (66)*w 110 + ((-22))*w 132 + (1)*w 153 + (1)*w 175 + ((-22))*w 176
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_177

theorem link3_178 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 42 w=rows3 w 178 := by
  change jetBlockRow (1) (1) 2 42 w=(121)*w 0 + (121)*w 6 + (121)*w 12 + (121)*w 18 + (121)*w 24 + (121)*w 30 + (121)*w 36 + (121)*w 42 + (121)*w 54 + (121)*w 60 + (66)*w 66 + (66)*w 72 + (66)*w 78 + (66)*w 84 + (66)*w 90 + (66)*w 96 + (66)*w 102 + (66)*w 108 + (66)*w 120 + (66)*w 126 + (18)*w 132 + (18)*w 138 + (1)*w 139 + (18)*w 144 + (1)*w 145 + (18)*w 150 + (1)*w 151 + (18)*w 156 + (1)*w 157 + (18)*w 162 + (1)*w 163 + (18)*w 168 + (1)*w 169 + (18)*w 174 + (1)*w 175 + (1)*w 181 + (18)*w 186 + (1)*w 187 + (18)*w 192 + (1)*w 193
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_178

theorem link3_179 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 43 w=rows3 w 179 := by
  change jetBlockRow (1) (1) 2 43 w=(121)*w 3 + (121)*w 15 + (121)*w 21 + (121)*w 27 + (121)*w 33 + (121)*w 39 + (121)*w 45 + (121)*w 51 + (121)*w 57 + (121)*w 63 + ((-33))*w 69 + ((-33))*w 81 + ((-33))*w 87 + ((-33))*w 93 + ((-33))*w 99 + ((-33))*w 105 + ((-33))*w 111 + ((-33))*w 117 + ((-33))*w 123 + ((-33))*w 129 + (9/2)*w 135 + (1)*w 136 + (1)*w 142 + (9/2)*w 147 + (1)*w 148 + (9/2)*w 153 + (1)*w 154 + (9/2)*w 159 + (1)*w 160 + (9/2)*w 165 + (1)*w 166 + (9/2)*w 171 + (1)*w 172 + (9/2)*w 177 + (1)*w 178 + (9/2)*w 183 + (1)*w 184 + (9/2)*w 189 + (1)*w 190 + (9/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_179

theorem link3_180 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 44 w=rows3 w 180 := by
  change jetBlockRow (1) (1) 2 44 w=(121)*w 3 + (121)*w 9 + (121)*w 15 + (121)*w 21 + (121)*w 27 + (121)*w 33 + (121)*w 39 + (121)*w 45 + (121)*w 51 + (121)*w 63 + (33)*w 69 + (33)*w 75 + (33)*w 81 + (33)*w 87 + (33)*w 93 + (33)*w 99 + (33)*w 105 + (33)*w 111 + (33)*w 117 + (33)*w 129 + (9/2)*w 135 + (1)*w 140 + (9/2)*w 141 + (1)*w 146 + (9/2)*w 147 + (1)*w 152 + (9/2)*w 153 + (1)*w 158 + (9/2)*w 159 + (1)*w 164 + (9/2)*w 165 + (1)*w 170 + (9/2)*w 171 + (1)*w 176 + (9/2)*w 177 + (1)*w 182 + (9/2)*w 183 + (1)*w 188 + (1)*w 194 + (9/2)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_180

theorem link3_181 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 45 w=rows3 w 181 := by
  change jetBlockRow (1) (1) 2 45 w=(121)*w 0 + (121)*w 6 + (121)*w 12 + (121)*w 24 + (121)*w 30 + (121)*w 36 + (121)*w 42 + (121)*w 48 + (121)*w 54 + (121)*w 60 + ((-66))*w 66 + ((-66))*w 72 + ((-66))*w 78 + ((-66))*w 90 + ((-66))*w 96 + ((-66))*w 102 + ((-66))*w 108 + ((-66))*w 114 + ((-66))*w 120 + ((-66))*w 126 + (18)*w 132 + (1)*w 137 + (18)*w 138 + (1)*w 143 + (18)*w 144 + (1)*w 149 + (1)*w 155 + (18)*w 156 + (1)*w 161 + (18)*w 162 + (1)*w 167 + (18)*w 168 + (1)*w 173 + (18)*w 174 + (1)*w 179 + (18)*w 180 + (1)*w 185 + (18)*w 186 + (1)*w 191 + (18)*w 192
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_181

theorem link3_182 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 46 w=rows3 w 182 := by
  change jetBlockRow (1) (1) 2 46 w=(1)*w 132
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_182

theorem link3_183 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 47 w=rows3 w 183 := by
  change jetBlockRow (1) (1) 2 47 w=(1)*w 154 + (1)*w 176
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_183

theorem link3_184 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 48 w=rows3 w 184 := by
  change jetBlockRow (1) (1) 2 48 w=(1)*w 143 + (1)*w 187
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_184

theorem link3_185 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 49 w=rows3 w 185 := by
  change jetBlockRow (1) (1) 2 49 w=(1)*w 138 + (1)*w 144 + (1)*w 150 + (1)*w 156 + (1)*w 162 + (1)*w 168 + (1)*w 174 + (1)*w 180 + (1)*w 186 + (1)*w 192
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_185

theorem link3_186 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 50 w=rows3 w 186 := by
  change jetBlockRow (1) (1) 2 50 w=(1)*w 141 + (2)*w 150 + (1)*w 174
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_186

theorem link3_187 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 51 w=rows3 w 187 := by
  change jetBlockRow (1) (1) 2 51 w=(1)*w 147 + (2)*w 162 + (1)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_187

theorem link3_188 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 52 w=rows3 w 188 := by
  change jetBlockRow (1) (1) 2 52 w=(1)*w 148 + (2)*w 164 + (1)*w 181
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_188

theorem link3_189 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 53 w=rows3 w 189 := by
  change jetBlockRow (1) (1) 2 53 w=(1)*w 149 + (2)*w 166 + (1)*w 182
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_189

theorem link3_190 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 54 w=rows3 w 190 := by
  change jetBlockRow (1) (1) 2 54 w=(1)*w 150 + (2)*w 168 + (1)*w 183
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_190

theorem link3_191 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 55 w=rows3 w 191 := by
  change jetBlockRow (1) (1) 2 55 w=(1)*w 137 + (2)*w 142 + (1)*w 170
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_191

theorem link3_192 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 56 w=rows3 w 192 := by
  change jetBlockRow (1) (1) 2 56 w=(1)*w 136 + (2)*w 140 + (1)*w 169
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_192

theorem link3_193 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 57 w=rows3 w 193 := by
  change jetBlockRow (1) (1) 2 57 w=(1)*w 139 + (7)*w 153 + (1)*w 161 + (1)*w 183 + (9)*w 195
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_193

theorem link3_194 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 58 w=rows3 w 194 := by
  change jetBlockRow (1) (1) 2 58 w=(1)*w 136 + (7)*w 144 + (1)*w 158 + (9)*w 168 + (1)*w 180
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_194

theorem link3_195 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 59 w=rows3 w 195 := by
  change jetBlockRow (1) (1) 2 59 w=(1)*w 145 + (2)*w 158 + (1)*w 178
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_195

theorem link3_196 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 60 w=rows3 w 196 := by
  change jetBlockRow (1) (1) 2 60 w=(1)*w 158 + (2)*w 184 + (1)*w 191
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_196

theorem link3_197 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 61 w=rows3 w 197 := by
  change jetBlockRow (1) (1) 2 61 w=(1)*w 151 + (2)*w 170 + (1)*w 184
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_197

theorem link3_198 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 62 w=rows3 w 198 := by
  change jetBlockRow (1) (1) 2 62 w=(1)*w 137 + (7)*w 147 + (1)*w 159 + (9)*w 177 + (1)*w 181
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_198

theorem link3_199 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 63 w=rows3 w 199 := by
  change jetBlockRow (1) (1) 2 63 w=(1)*w 139 + (2)*w 146 + (1)*w 172
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_199

theorem link3_200 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 64 w=rows3 w 200 := by
  change jetBlockRow (1) (1) 2 64 w=(1)*w 140 + (2)*w 148 + (1)*w 173
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_200

theorem link3_201 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 65 w=rows3 w 201 := by
  change jetBlockRow (1) (1) 2 65 w=(1)*w 146 + (2)*w 160 + (1)*w 179
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_201

theorem link3_202 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 66 w=rows3 w 202 := by
  change jetBlockRow (1) (1) 2 66 w=(1)*w 138 + (2)*w 144 + (1)*w 171
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_202

theorem link3_203 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 2 67 w=rows3 w 203 := by
  change jetBlockRow (1) (1) 2 67 w=(1)*w 160 + (2)*w 188 + (1)*w 193
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_203

theorem link3_204 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 0 w=rows3 w 204 := by
  change jetBlockRow (1) (1) 3 0 w=((-11)/3)*w 63 + ((-1)/2)*w 129 + ((-1)/22)*w 195 + (1)*w 198 + ((-1)/484)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_204

theorem link3_205 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 1 w=rows3 w 205 := by
  change jetBlockRow (1) (1) 3 1 w=((-242))*w 0 + ((-2178))*w 66 + ((-13068))*w 132 + ((-39204))*w 198 + (1)*w 199
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_205

theorem link3_206 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 2 w=rows3 w 206 := by
  change jetBlockRow (1) (1) 3 2 w=((-242)/3)*w 0 + ((-242))*w 66 + ((-484))*w 132 + ((-484))*w 198 + (1)*w 201
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_206

theorem link3_207 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 3 w=rows3 w 207 := by
  change jetBlockRow (1) (1) 3 3 w=(242)*w 0 + ((-2178))*w 66 + (13068)*w 132 + ((-39204))*w 198 + (1)*w 263
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_207

theorem link3_208 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 4 w=rows3 w 208 := by
  change jetBlockRow (1) (1) 3 4 w=(166375/9)*w 65 + ((-3025)/18)*w 131 + (55/54)*w 197 + (1)*w 228 + ((-1)/324)*w 263
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_208

theorem link3_209 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 5 w=rows3 w 209 := by
  change jetBlockRow (1) (1) 3 5 w=(332750/3)*w 0 + ((-6050))*w 66 + (220)*w 132 + ((-4))*w 198 + (1)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_209

theorem link3_210 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 6 w=rows3 w 210 := by
  change jetBlockRow (1) (1) 3 6 w=((-22)/9)*w 64 + ((-2)/9)*w 130 + ((-4)/297)*w 196 + (1)*w 231 + ((-4)/9801)*w 262
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_210

theorem link3_211 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 7 w=rows3 w 211 := by
  change jetBlockRow (1) (1) 3 7 w=((-121))*w 33 + ((-1089)/2)*w 99 + ((-3267)/2)*w 165 + (1)*w 200 + ((-9801)/4)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_211

theorem link3_212 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 8 w=rows3 w 212 := by
  change jetBlockRow (1) (1) 3 8 w=((-121)/3)*w 33 + ((-121)/2)*w 99 + ((-121)/2)*w 165 + (1)*w 204 + ((-121)/4)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_212

theorem link3_213 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 9 w=rows3 w 213 := by
  change jetBlockRow (1) (1) 3 9 w=((-22)/3)*w 60 + ((-2))*w 126 + ((-4)/11)*w 192 + (1)*w 231 + ((-4)/121)*w 258
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_213

theorem link3_214 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 10 w=rows3 w 214 := by
  change jetBlockRow (1) (1) 3 10 w=((-166375))*w 63 + ((-27225)/2)*w 129 + ((-1485)/2)*w 195 + (1)*w 232 + ((-81)/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_214

theorem link3_215 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 11 w=rows3 w 215 := by
  change jetBlockRow (1) (1) 3 11 w=(11979)*w 65 + ((-1089)/2)*w 131 + (33/2)*w 197 + (1)*w 230 + ((-1)/4)*w 263
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_215

theorem link3_216 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 12 w=rows3 w 216 := by
  change jetBlockRow (1) (1) 3 12 w=((-11979))*w 63 + ((-1089)/2)*w 129 + ((-33)/2)*w 195 + (1)*w 234 + ((-1)/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_216

theorem link3_217 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 13 w=rows3 w 217 := by
  change jetBlockRow (1) (1) 3 13 w=((-242)/9)*w 44 + ((-242)/9)*w 110 + ((-484)/27)*w 176 + (1)*w 207 + ((-484)/81)*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_217

theorem link3_218 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 14 w=rows3 w 218 := by
  change jetBlockRow (1) (1) 3 14 w=((-22))*w 48 + ((-18))*w 114 + ((-108)/11)*w 180 + (1)*w 209 + ((-324)/121)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_218

theorem link3_219 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 15 w=rows3 w 219 := by
  change jetBlockRow (1) (1) 3 15 w=((-121)/9)*w 55 + ((-121)/18)*w 121 + ((-121)/54)*w 187 + (1)*w 216 + ((-121)/324)*w 253
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_219

theorem link3_220 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 16 w=rows3 w 220 := by
  change jetBlockRow (1) (1) 3 16 w=((-11))*w 57 + ((-9)/2)*w 123 + ((-27)/22)*w 189 + (1)*w 220 + ((-81)/484)*w 255
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_220

theorem link3_221 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 17 w=rows3 w 221 := by
  change jetBlockRow (1) (1) 3 17 w=(5324/9)*w 4 + ((-242)/9)*w 70 + (22/27)*w 136 + ((-1)/81)*w 202 + (1)*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_221

theorem link3_222 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 18 w=rows3 w 222 := by
  change jetBlockRow (1) (1) 3 18 w=(5324)*w 12 + ((-2178))*w 78 + (594)*w 144 + ((-81))*w 210 + (1)*w 260
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_222

theorem link3_223 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 19 w=rows3 w 223 := by
  change jetBlockRow (1) (1) 3 19 w=((-23958))*w 62 + ((-2178))*w 128 + ((-132))*w 194 + (1)*w 233 + ((-4))*w 260
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_223

theorem link3_224 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 20 w=rows3 w 224 := by
  change jetBlockRow (1) (1) 3 20 w=(1331/9)*w 61 + ((-121)/18)*w 127 + (11/54)*w 193 + (1)*w 216 + ((-1)/324)*w 259
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_224

theorem link3_225 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 21 w=rows3 w 225 := by
  change jetBlockRow (1) (1) 3 21 w=(2662/9)*w 62 + ((-242)/9)*w 128 + (44/27)*w 194 + (1)*w 225 + ((-4)/81)*w 260
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_225

theorem link3_226 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 22 w=rows3 w 226 := by
  change jetBlockRow (1) (1) 3 22 w=((-2662))*w 42 + ((-2178))*w 108 + ((-1188))*w 174 + (1)*w 235 + ((-324))*w 240
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_226

theorem link3_227 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 23 w=rows3 w 227 := by
  change jetBlockRow (1) (1) 3 23 w=((-1331))*w 51 + ((-1089)/2)*w 117 + ((-297)/2)*w 183 + (1)*w 236 + ((-81)/4)*w 249
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_227

theorem link3_228 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 24 w=rows3 w 228 := by
  change jetBlockRow (1) (1) 3 24 w=((-2662)/3)*w 54 + ((-242))*w 120 + ((-44))*w 186 + (1)*w 237 + ((-4))*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_228

theorem link3_229 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 25 w=rows3 w 229 := by
  change jetBlockRow (1) (1) 3 25 w=((-1331)/3)*w 57 + ((-121)/2)*w 123 + ((-11)/2)*w 189 + (1)*w 240 + ((-1)/4)*w 255
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_229

theorem link3_230 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 26 w=rows3 w 230 := by
  change jetBlockRow (1) (1) 3 26 w=((-2662)/9)*w 58 + ((-242)/9)*w 124 + ((-44)/27)*w 190 + (1)*w 243 + ((-4)/81)*w 256
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_230

theorem link3_231 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 27 w=rows3 w 231 := by
  change jetBlockRow (1) (1) 3 27 w=((-1331)/9)*w 59 + ((-121)/18)*w 125 + ((-11)/54)*w 191 + (1)*w 252 + ((-1)/324)*w 257
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_231

theorem link3_232 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 28 w=rows3 w 232 := by
  change jetBlockRow (1) (1) 3 28 w=(1331/9)*w 7 + ((-121)/18)*w 73 + (11/54)*w 139 + ((-1)/324)*w 205 + (1)*w 210
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_232

theorem link3_233 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 29 w=rows3 w 233 := by
  change jetBlockRow (1) (1) 3 29 w=(2662/9)*w 8 + ((-242)/9)*w 74 + (44/27)*w 140 + ((-4)/81)*w 206 + (1)*w 219
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_233

theorem link3_234 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 30 w=rows3 w 234 := by
  change jetBlockRow (1) (1) 3 30 w=(1331/3)*w 9 + ((-121)/2)*w 75 + (11/2)*w 141 + ((-1)/4)*w 207 + (1)*w 222
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_234

theorem link3_235 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 31 w=rows3 w 235 := by
  change jetBlockRow (1) (1) 3 31 w=(1331)*w 15 + ((-1089)/2)*w 81 + (297/2)*w 147 + ((-81)/4)*w 213 + (1)*w 226
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_235

theorem link3_236 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 32 w=rows3 w 236 := by
  change jetBlockRow (1) (1) 3 32 w=(2662)*w 24 + ((-2178))*w 90 + (1188)*w 156 + ((-324))*w 222 + (1)*w 227
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_236

theorem link3_237 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 33 w=rows3 w 237 := by
  change jetBlockRow (1) (1) 3 33 w=((-2662))*w 54 + ((-2178))*w 120 + ((-1188))*w 186 + (1)*w 229 + ((-324))*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_237

theorem link3_238 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 34 w=rows3 w 238 := by
  change jetBlockRow (1) (1) 3 34 w=((-1331)/9)*w 5 + ((-121)/18)*w 71 + ((-11)/54)*w 137 + ((-1)/324)*w 203 + (1)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_238

theorem link3_239 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 35 w=rows3 w 239 := by
  change jetBlockRow (1) (1) 3 35 w=((-1089))*w 11 + ((-1089))*w 33 + ((-1089)/2)*w 77 + ((-1089)/2)*w 99 + ((-363)/2)*w 143 + ((-363)/2)*w 165 + ((-121)/4)*w 209 + (1)*w 222 + ((-121)/4)*w 231 + (1)*w 244
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_239

theorem link3_240 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 36 w=rows3 w 240 := by
  change jetBlockRow (1) (1) 3 36 w=(1089)*w 33 + (1089)*w 55 + ((-1089)/2)*w 99 + ((-1089)/2)*w 121 + (363/2)*w 165 + (363/2)*w 187 + (1)*w 218 + ((-121)/4)*w 231 + (1)*w 240 + ((-121)/4)*w 253
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_240

theorem link3_241 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 37 w=rows3 w 241 := by
  change jetBlockRow (1) (1) 3 37 w=(2662/3)*w 0 + (2662/3)*w 6 + (2662/3)*w 12 + (2662/3)*w 18 + (2662/3)*w 24 + (2662/3)*w 30 + (2662/3)*w 36 + (2662/3)*w 42 + (2662/3)*w 48 + (2662/3)*w 54 + (242)*w 66 + (242)*w 72 + (242)*w 78 + (242)*w 84 + (242)*w 90 + (242)*w 96 + (242)*w 102 + (242)*w 108 + (242)*w 114 + (242)*w 120 + (44)*w 132 + (44)*w 138 + (44)*w 144 + (44)*w 150 + (44)*w 156 + (44)*w 162 + (44)*w 168 + (44)*w 174 + (44)*w 180 + (44)*w 186 + (4)*w 198 + (4)*w 204 + (1)*w 207 + (4)*w 210 + (1)*w 213 + (4)*w 216 + (1)*w 219 + (4)*w 222 + (1)*w 225 + (4)*w 228 + (1)*w 231 + (4)*w 234 + (1)*w 237 + (4)*w 240 + (1)*w 243 + (4)*w 246 + (1)*w 249 + (4)*w 252 + (1)*w 255 + (1)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_241

theorem link3_242 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 38 w=rows3 w 242 := by
  change jetBlockRow (1) (1) 3 38 w=(4356)*w 0 + (4356)*w 22 + ((-2178))*w 66 + ((-2178))*w 88 + (726)*w 132 + (726)*w 154 + ((-121))*w 198 + (1)*w 208 + ((-121))*w 220 + (1)*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_242

theorem link3_243 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 39 w=rows3 w 243 := by
  change jetBlockRow (1) (1) 3 39 w=((-4356))*w 0 + ((-4356))*w 44 + ((-2178))*w 66 + ((-2178))*w 110 + ((-726))*w 132 + ((-726))*w 176 + ((-121))*w 198 + (1)*w 210 + ((-121))*w 242 + (1)*w 254
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_243

theorem link3_244 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 40 w=rows3 w 244 := by
  change jetBlockRow (1) (1) 3 40 w=((-2178))*w 0 + ((-2178))*w 22 + ((-2178))*w 66 + ((-2178))*w 88 + ((-1452))*w 132 + ((-1452))*w 154 + ((-484))*w 198 + ((-484))*w 220 + (1)*w 221 + (1)*w 243
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_244

theorem link3_245 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 41 w=rows3 w 245 := by
  change jetBlockRow (1) (1) 3 41 w=(2178)*w 0 + (2178)*w 44 + ((-2178))*w 66 + ((-2178))*w 110 + (1452)*w 132 + (1452)*w 176 + ((-484))*w 198 + (1)*w 219 + (1)*w 241 + ((-484))*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_245

theorem link3_246 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 42 w=rows3 w 246 := by
  change jetBlockRow (1) (1) 3 42 w=(2662)*w 0 + (2662)*w 6 + (2662)*w 12 + (2662)*w 18 + (2662)*w 24 + (2662)*w 30 + (2662)*w 36 + (2662)*w 42 + (2662)*w 54 + (2662)*w 60 + (2178)*w 66 + (2178)*w 72 + (2178)*w 78 + (2178)*w 84 + (2178)*w 90 + (2178)*w 96 + (2178)*w 102 + (2178)*w 108 + (2178)*w 120 + (2178)*w 126 + (1188)*w 132 + (1188)*w 138 + (1188)*w 144 + (1188)*w 150 + (1188)*w 156 + (1188)*w 162 + (1188)*w 168 + (1188)*w 174 + (1188)*w 186 + (1188)*w 192 + (324)*w 198 + (324)*w 204 + (1)*w 205 + (324)*w 210 + (1)*w 211 + (324)*w 216 + (1)*w 217 + (324)*w 222 + (1)*w 223 + (324)*w 228 + (1)*w 229 + (324)*w 234 + (1)*w 235 + (324)*w 240 + (1)*w 241 + (1)*w 247 + (324)*w 252 + (1)*w 253 + (324)*w 258 + (1)*w 259
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_246

theorem link3_247 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 43 w=rows3 w 247 := by
  change jetBlockRow (1) (1) 3 43 w=((-1331))*w 3 + ((-1331))*w 15 + ((-1331))*w 21 + ((-1331))*w 27 + ((-1331))*w 33 + ((-1331))*w 39 + ((-1331))*w 45 + ((-1331))*w 51 + ((-1331))*w 57 + ((-1331))*w 63 + (1089/2)*w 69 + (1089/2)*w 81 + (1089/2)*w 87 + (1089/2)*w 93 + (1089/2)*w 99 + (1089/2)*w 105 + (1089/2)*w 111 + (1089/2)*w 117 + (1089/2)*w 123 + (1089/2)*w 129 + ((-297)/2)*w 135 + ((-297)/2)*w 147 + ((-297)/2)*w 153 + ((-297)/2)*w 159 + ((-297)/2)*w 165 + ((-297)/2)*w 171 + ((-297)/2)*w 177 + ((-297)/2)*w 183 + ((-297)/2)*w 189 + ((-297)/2)*w 195 + (81/4)*w 201 + (1)*w 202 + (1)*w 208 + (81/4)*w 213 + (1)*w 214 + (81/4)*w 219 + (1)*w 220 + (81/4)*w 225 + (1)*w 226 + (81/4)*w 231 + (1)*w 232 + (81/4)*w 237 + (1)*w 238 + (81/4)*w 243 + (1)*w 244 + (81/4)*w 249 + (1)*w 250 + (81/4)*w 255 + (1)*w 256 + (81/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_247

theorem link3_248 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 44 w=rows3 w 248 := by
  change jetBlockRow (1) (1) 3 44 w=(1331)*w 3 + (1331)*w 9 + (1331)*w 15 + (1331)*w 21 + (1331)*w 27 + (1331)*w 33 + (1331)*w 39 + (1331)*w 45 + (1331)*w 51 + (1331)*w 63 + (1089/2)*w 69 + (1089/2)*w 75 + (1089/2)*w 81 + (1089/2)*w 87 + (1089/2)*w 93 + (1089/2)*w 99 + (1089/2)*w 105 + (1089/2)*w 111 + (1089/2)*w 117 + (1089/2)*w 129 + (297/2)*w 135 + (297/2)*w 141 + (297/2)*w 147 + (297/2)*w 153 + (297/2)*w 159 + (297/2)*w 165 + (297/2)*w 171 + (297/2)*w 177 + (297/2)*w 183 + (297/2)*w 195 + (81/4)*w 201 + (1)*w 206 + (81/4)*w 207 + (1)*w 212 + (81/4)*w 213 + (1)*w 218 + (81/4)*w 219 + (1)*w 224 + (81/4)*w 225 + (1)*w 230 + (81/4)*w 231 + (1)*w 236 + (81/4)*w 237 + (1)*w 242 + (81/4)*w 243 + (1)*w 248 + (81/4)*w 249 + (1)*w 254 + (1)*w 260 + (81/4)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_248

theorem link3_249 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 45 w=rows3 w 249 := by
  change jetBlockRow (1) (1) 3 45 w=((-2662))*w 0 + ((-2662))*w 6 + ((-2662))*w 12 + ((-2662))*w 24 + ((-2662))*w 30 + ((-2662))*w 36 + ((-2662))*w 42 + ((-2662))*w 48 + ((-2662))*w 54 + ((-2662))*w 60 + (2178)*w 66 + (2178)*w 72 + (2178)*w 78 + (2178)*w 90 + (2178)*w 96 + (2178)*w 102 + (2178)*w 108 + (2178)*w 114 + (2178)*w 120 + (2178)*w 126 + ((-1188))*w 132 + ((-1188))*w 138 + ((-1188))*w 144 + ((-1188))*w 156 + ((-1188))*w 162 + ((-1188))*w 168 + ((-1188))*w 174 + ((-1188))*w 180 + ((-1188))*w 186 + ((-1188))*w 192 + (324)*w 198 + (1)*w 203 + (324)*w 204 + (1)*w 209 + (324)*w 210 + (1)*w 215 + (1)*w 221 + (324)*w 222 + (1)*w 227 + (324)*w 228 + (1)*w 233 + (324)*w 234 + (1)*w 239 + (324)*w 240 + (1)*w 245 + (324)*w 246 + (1)*w 251 + (324)*w 252 + (1)*w 257 + (324)*w 258
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_249

theorem link3_250 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 46 w=rows3 w 250 := by
  change jetBlockRow (1) (1) 3 46 w=(1)*w 198
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_250

theorem link3_251 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 47 w=rows3 w 251 := by
  change jetBlockRow (1) (1) 3 47 w=(1)*w 220 + (1)*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_251

theorem link3_252 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 48 w=rows3 w 252 := by
  change jetBlockRow (1) (1) 3 48 w=(1)*w 209 + (1)*w 253
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_252

theorem link3_253 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 49 w=rows3 w 253 := by
  change jetBlockRow (1) (1) 3 49 w=(1)*w 204 + (1)*w 210 + (1)*w 216 + (1)*w 222 + (1)*w 228 + (1)*w 234 + (1)*w 240 + (1)*w 246 + (1)*w 252 + (1)*w 258
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_253

theorem link3_254 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 50 w=rows3 w 254 := by
  change jetBlockRow (1) (1) 3 50 w=(1)*w 207 + (4)*w 216 + (1)*w 240
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_254

theorem link3_255 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 51 w=rows3 w 255 := by
  change jetBlockRow (1) (1) 3 51 w=(1)*w 213 + (4)*w 228 + (1)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_255

theorem link3_256 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 52 w=rows3 w 256 := by
  change jetBlockRow (1) (1) 3 52 w=(1)*w 214 + (4)*w 230 + (1)*w 247
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_256

theorem link3_257 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 53 w=rows3 w 257 := by
  change jetBlockRow (1) (1) 3 53 w=(1)*w 215 + (4)*w 232 + (1)*w 248
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_257

theorem link3_258 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 54 w=rows3 w 258 := by
  change jetBlockRow (1) (1) 3 54 w=(1)*w 216 + (4)*w 234 + (1)*w 249
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_258

theorem link3_259 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 55 w=rows3 w 259 := by
  change jetBlockRow (1) (1) 3 55 w=(1)*w 203 + (4)*w 208 + (1)*w 236
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_259

theorem link3_260 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 56 w=rows3 w 260 := by
  change jetBlockRow (1) (1) 3 56 w=(1)*w 202 + (4)*w 206 + (1)*w 235
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_260

theorem link3_261 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 57 w=rows3 w 261 := by
  change jetBlockRow (1) (1) 3 57 w=(1)*w 205 + (21)*w 219 + (1)*w 227 + (1)*w 249 + (81)*w 261
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_261

theorem link3_262 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 58 w=rows3 w 262 := by
  change jetBlockRow (1) (1) 3 58 w=(1)*w 202 + (21)*w 210 + (1)*w 224 + (81)*w 234 + (1)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_262

theorem link3_263 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 59 w=rows3 w 263 := by
  change jetBlockRow (1) (1) 3 59 w=(1)*w 211 + (4)*w 224 + (1)*w 244
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_263

theorem link3_264 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 60 w=rows3 w 264 := by
  change jetBlockRow (1) (1) 3 60 w=(1)*w 224 + (4)*w 250 + (1)*w 257
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_264

theorem link3_265 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 61 w=rows3 w 265 := by
  change jetBlockRow (1) (1) 3 61 w=(1)*w 217 + (4)*w 236 + (1)*w 250
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_265

theorem link3_266 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 62 w=rows3 w 266 := by
  change jetBlockRow (1) (1) 3 62 w=(1)*w 203 + (21)*w 213 + (1)*w 225 + (81)*w 243 + (1)*w 247
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_266

theorem link3_267 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 63 w=rows3 w 267 := by
  change jetBlockRow (1) (1) 3 63 w=(1)*w 205 + (4)*w 212 + (1)*w 238
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_267

theorem link3_268 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 64 w=rows3 w 268 := by
  change jetBlockRow (1) (1) 3 64 w=(1)*w 206 + (4)*w 214 + (1)*w 239
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_268

theorem link3_269 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 65 w=rows3 w 269 := by
  change jetBlockRow (1) (1) 3 65 w=(1)*w 212 + (4)*w 226 + (1)*w 245
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_269

theorem link3_270 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 66 w=rows3 w 270 := by
  change jetBlockRow (1) (1) 3 66 w=(1)*w 204 + (4)*w 210 + (1)*w 237
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_270

theorem link3_271 (w : Fin 264→ℂ) : jetBlockRow (1) (1) 3 67 w=rows3 w 271 := by
  change jetBlockRow (1) (1) 3 67 w=(1)*w 226 + (4)*w 254 + (1)*w 259
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link3_271

end SmallLevelTwentyTwoJetBlock
end
end
end

/-! ## SmallLevelTwentyTwoJetBlockKernelCaseBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoJetBlock
open Complex SmallLevelFiniteShift SmallLevelTwentyTwoLaurent SmallLevelTwentyTwoThirdJet

theorem kernel_case0 (w : Fin 264→ℂ) (hw : ∀ n i, jetBlockRow (-1) (-1) n i w=0) : w=0 := by
  apply SmallLevelTwentyTwoThirdJet.kernel0 w
  intro r
  fin_cases r
  · exact (link0_0 w).symm.trans (hw 0 0)
  · exact (link0_1 w).symm.trans (hw 0 1)
  · exact (link0_2 w).symm.trans (hw 0 2)
  · exact (link0_3 w).symm.trans (hw 0 3)
  · exact (link0_4 w).symm.trans (hw 0 4)
  · exact (link0_5 w).symm.trans (hw 0 5)
  · exact (link0_6 w).symm.trans (hw 0 6)
  · exact (link0_7 w).symm.trans (hw 0 7)
  · exact (link0_8 w).symm.trans (hw 0 8)
  · exact (link0_9 w).symm.trans (hw 0 9)
  · exact (link0_10 w).symm.trans (hw 0 10)
  · exact (link0_11 w).symm.trans (hw 0 11)
  · exact (link0_12 w).symm.trans (hw 0 12)
  · exact (link0_13 w).symm.trans (hw 0 13)
  · exact (link0_14 w).symm.trans (hw 0 14)
  · exact (link0_15 w).symm.trans (hw 0 15)
  · exact (link0_16 w).symm.trans (hw 0 16)
  · exact (link0_17 w).symm.trans (hw 0 17)
  · exact (link0_18 w).symm.trans (hw 0 18)
  · exact (link0_19 w).symm.trans (hw 0 19)
  · exact (link0_20 w).symm.trans (hw 0 20)
  · exact (link0_21 w).symm.trans (hw 0 21)
  · exact (link0_22 w).symm.trans (hw 0 22)
  · exact (link0_23 w).symm.trans (hw 0 23)
  · exact (link0_24 w).symm.trans (hw 0 24)
  · exact (link0_25 w).symm.trans (hw 0 25)
  · exact (link0_26 w).symm.trans (hw 0 26)
  · exact (link0_27 w).symm.trans (hw 0 27)
  · exact (link0_28 w).symm.trans (hw 0 28)
  · exact (link0_29 w).symm.trans (hw 0 29)
  · exact (link0_30 w).symm.trans (hw 0 30)
  · exact (link0_31 w).symm.trans (hw 0 31)
  · exact (link0_32 w).symm.trans (hw 0 32)
  · exact (link0_33 w).symm.trans (hw 0 33)
  · exact (link0_34 w).symm.trans (hw 0 34)
  · exact (link0_35 w).symm.trans (hw 0 35)
  · exact (link0_36 w).symm.trans (hw 0 36)
  · exact (link0_37 w).symm.trans (hw 0 37)
  · exact (link0_38 w).symm.trans (hw 0 38)
  · exact (link0_39 w).symm.trans (hw 0 39)
  · exact (link0_40 w).symm.trans (hw 0 40)
  · exact (link0_41 w).symm.trans (hw 0 41)
  · exact (link0_42 w).symm.trans (hw 0 42)
  · exact (link0_43 w).symm.trans (hw 0 43)
  · exact (link0_44 w).symm.trans (hw 0 44)
  · exact (link0_45 w).symm.trans (hw 0 45)
  · exact (link0_46 w).symm.trans (hw 0 46)
  · exact (link0_47 w).symm.trans (hw 0 47)
  · exact (link0_48 w).symm.trans (hw 0 48)
  · exact (link0_49 w).symm.trans (hw 0 49)
  · exact (link0_50 w).symm.trans (hw 0 50)
  · exact (link0_51 w).symm.trans (hw 0 51)
  · exact (link0_52 w).symm.trans (hw 0 52)
  · exact (link0_53 w).symm.trans (hw 0 53)
  · exact (link0_54 w).symm.trans (hw 0 54)
  · exact (link0_55 w).symm.trans (hw 0 55)
  · exact (link0_56 w).symm.trans (hw 0 56)
  · exact (link0_57 w).symm.trans (hw 0 57)
  · exact (link0_58 w).symm.trans (hw 0 58)
  · exact (link0_59 w).symm.trans (hw 0 59)
  · exact (link0_60 w).symm.trans (hw 0 60)
  · exact (link0_61 w).symm.trans (hw 0 61)
  · exact (link0_62 w).symm.trans (hw 0 62)
  · exact (link0_63 w).symm.trans (hw 0 63)
  · exact (link0_64 w).symm.trans (hw 0 64)
  · exact (link0_65 w).symm.trans (hw 0 65)
  · exact (link0_66 w).symm.trans (hw 0 66)
  · exact (link0_67 w).symm.trans (hw 0 67)
  · exact (link0_68 w).symm.trans (hw 1 0)
  · exact (link0_69 w).symm.trans (hw 1 1)
  · exact (link0_70 w).symm.trans (hw 1 2)
  · exact (link0_71 w).symm.trans (hw 1 3)
  · exact (link0_72 w).symm.trans (hw 1 4)
  · exact (link0_73 w).symm.trans (hw 1 5)
  · exact (link0_74 w).symm.trans (hw 1 6)
  · exact (link0_75 w).symm.trans (hw 1 7)
  · exact (link0_76 w).symm.trans (hw 1 8)
  · exact (link0_77 w).symm.trans (hw 1 9)
  · exact (link0_78 w).symm.trans (hw 1 10)
  · exact (link0_79 w).symm.trans (hw 1 11)
  · exact (link0_80 w).symm.trans (hw 1 12)
  · exact (link0_81 w).symm.trans (hw 1 13)
  · exact (link0_82 w).symm.trans (hw 1 14)
  · exact (link0_83 w).symm.trans (hw 1 15)
  · exact (link0_84 w).symm.trans (hw 1 16)
  · exact (link0_85 w).symm.trans (hw 1 17)
  · exact (link0_86 w).symm.trans (hw 1 18)
  · exact (link0_87 w).symm.trans (hw 1 19)
  · exact (link0_88 w).symm.trans (hw 1 20)
  · exact (link0_89 w).symm.trans (hw 1 21)
  · exact (link0_90 w).symm.trans (hw 1 22)
  · exact (link0_91 w).symm.trans (hw 1 23)
  · exact (link0_92 w).symm.trans (hw 1 24)
  · exact (link0_93 w).symm.trans (hw 1 25)
  · exact (link0_94 w).symm.trans (hw 1 26)
  · exact (link0_95 w).symm.trans (hw 1 27)
  · exact (link0_96 w).symm.trans (hw 1 28)
  · exact (link0_97 w).symm.trans (hw 1 29)
  · exact (link0_98 w).symm.trans (hw 1 30)
  · exact (link0_99 w).symm.trans (hw 1 31)
  · exact (link0_100 w).symm.trans (hw 1 32)
  · exact (link0_101 w).symm.trans (hw 1 33)
  · exact (link0_102 w).symm.trans (hw 1 34)
  · exact (link0_103 w).symm.trans (hw 1 35)
  · exact (link0_104 w).symm.trans (hw 1 36)
  · exact (link0_105 w).symm.trans (hw 1 37)
  · exact (link0_106 w).symm.trans (hw 1 38)
  · exact (link0_107 w).symm.trans (hw 1 39)
  · exact (link0_108 w).symm.trans (hw 1 40)
  · exact (link0_109 w).symm.trans (hw 1 41)
  · exact (link0_110 w).symm.trans (hw 1 42)
  · exact (link0_111 w).symm.trans (hw 1 43)
  · exact (link0_112 w).symm.trans (hw 1 44)
  · exact (link0_113 w).symm.trans (hw 1 45)
  · exact (link0_114 w).symm.trans (hw 1 46)
  · exact (link0_115 w).symm.trans (hw 1 47)
  · exact (link0_116 w).symm.trans (hw 1 48)
  · exact (link0_117 w).symm.trans (hw 1 49)
  · exact (link0_118 w).symm.trans (hw 1 50)
  · exact (link0_119 w).symm.trans (hw 1 51)
  · exact (link0_120 w).symm.trans (hw 1 52)
  · exact (link0_121 w).symm.trans (hw 1 53)
  · exact (link0_122 w).symm.trans (hw 1 54)
  · exact (link0_123 w).symm.trans (hw 1 55)
  · exact (link0_124 w).symm.trans (hw 1 56)
  · exact (link0_125 w).symm.trans (hw 1 57)
  · exact (link0_126 w).symm.trans (hw 1 58)
  · exact (link0_127 w).symm.trans (hw 1 59)
  · exact (link0_128 w).symm.trans (hw 1 60)
  · exact (link0_129 w).symm.trans (hw 1 61)
  · exact (link0_130 w).symm.trans (hw 1 62)
  · exact (link0_131 w).symm.trans (hw 1 63)
  · exact (link0_132 w).symm.trans (hw 1 64)
  · exact (link0_133 w).symm.trans (hw 1 65)
  · exact (link0_134 w).symm.trans (hw 1 66)
  · exact (link0_135 w).symm.trans (hw 1 67)
  · exact (link0_136 w).symm.trans (hw 2 0)
  · exact (link0_137 w).symm.trans (hw 2 1)
  · exact (link0_138 w).symm.trans (hw 2 2)
  · exact (link0_139 w).symm.trans (hw 2 3)
  · exact (link0_140 w).symm.trans (hw 2 4)
  · exact (link0_141 w).symm.trans (hw 2 5)
  · exact (link0_142 w).symm.trans (hw 2 6)
  · exact (link0_143 w).symm.trans (hw 2 7)
  · exact (link0_144 w).symm.trans (hw 2 8)
  · exact (link0_145 w).symm.trans (hw 2 9)
  · exact (link0_146 w).symm.trans (hw 2 10)
  · exact (link0_147 w).symm.trans (hw 2 11)
  · exact (link0_148 w).symm.trans (hw 2 12)
  · exact (link0_149 w).symm.trans (hw 2 13)
  · exact (link0_150 w).symm.trans (hw 2 14)
  · exact (link0_151 w).symm.trans (hw 2 15)
  · exact (link0_152 w).symm.trans (hw 2 16)
  · exact (link0_153 w).symm.trans (hw 2 17)
  · exact (link0_154 w).symm.trans (hw 2 18)
  · exact (link0_155 w).symm.trans (hw 2 19)
  · exact (link0_156 w).symm.trans (hw 2 20)
  · exact (link0_157 w).symm.trans (hw 2 21)
  · exact (link0_158 w).symm.trans (hw 2 22)
  · exact (link0_159 w).symm.trans (hw 2 23)
  · exact (link0_160 w).symm.trans (hw 2 24)
  · exact (link0_161 w).symm.trans (hw 2 25)
  · exact (link0_162 w).symm.trans (hw 2 26)
  · exact (link0_163 w).symm.trans (hw 2 27)
  · exact (link0_164 w).symm.trans (hw 2 28)
  · exact (link0_165 w).symm.trans (hw 2 29)
  · exact (link0_166 w).symm.trans (hw 2 30)
  · exact (link0_167 w).symm.trans (hw 2 31)
  · exact (link0_168 w).symm.trans (hw 2 32)
  · exact (link0_169 w).symm.trans (hw 2 33)
  · exact (link0_170 w).symm.trans (hw 2 34)
  · exact (link0_171 w).symm.trans (hw 2 35)
  · exact (link0_172 w).symm.trans (hw 2 36)
  · exact (link0_173 w).symm.trans (hw 2 37)
  · exact (link0_174 w).symm.trans (hw 2 38)
  · exact (link0_175 w).symm.trans (hw 2 39)
  · exact (link0_176 w).symm.trans (hw 2 40)
  · exact (link0_177 w).symm.trans (hw 2 41)
  · exact (link0_178 w).symm.trans (hw 2 42)
  · exact (link0_179 w).symm.trans (hw 2 43)
  · exact (link0_180 w).symm.trans (hw 2 44)
  · exact (link0_181 w).symm.trans (hw 2 45)
  · exact (link0_182 w).symm.trans (hw 2 46)
  · exact (link0_183 w).symm.trans (hw 2 47)
  · exact (link0_184 w).symm.trans (hw 2 48)
  · exact (link0_185 w).symm.trans (hw 2 49)
  · exact (link0_186 w).symm.trans (hw 2 50)
  · exact (link0_187 w).symm.trans (hw 2 51)
  · exact (link0_188 w).symm.trans (hw 2 52)
  · exact (link0_189 w).symm.trans (hw 2 53)
  · exact (link0_190 w).symm.trans (hw 2 54)
  · exact (link0_191 w).symm.trans (hw 2 55)
  · exact (link0_192 w).symm.trans (hw 2 56)
  · exact (link0_193 w).symm.trans (hw 2 57)
  · exact (link0_194 w).symm.trans (hw 2 58)
  · exact (link0_195 w).symm.trans (hw 2 59)
  · exact (link0_196 w).symm.trans (hw 2 60)
  · exact (link0_197 w).symm.trans (hw 2 61)
  · exact (link0_198 w).symm.trans (hw 2 62)
  · exact (link0_199 w).symm.trans (hw 2 63)
  · exact (link0_200 w).symm.trans (hw 2 64)
  · exact (link0_201 w).symm.trans (hw 2 65)
  · exact (link0_202 w).symm.trans (hw 2 66)
  · exact (link0_203 w).symm.trans (hw 2 67)
  · exact (link0_204 w).symm.trans (hw 3 0)
  · exact (link0_205 w).symm.trans (hw 3 1)
  · exact (link0_206 w).symm.trans (hw 3 2)
  · exact (link0_207 w).symm.trans (hw 3 3)
  · exact (link0_208 w).symm.trans (hw 3 4)
  · exact (link0_209 w).symm.trans (hw 3 5)
  · exact (link0_210 w).symm.trans (hw 3 6)
  · exact (link0_211 w).symm.trans (hw 3 7)
  · exact (link0_212 w).symm.trans (hw 3 8)
  · exact (link0_213 w).symm.trans (hw 3 9)
  · exact (link0_214 w).symm.trans (hw 3 10)
  · exact (link0_215 w).symm.trans (hw 3 11)
  · exact (link0_216 w).symm.trans (hw 3 12)
  · exact (link0_217 w).symm.trans (hw 3 13)
  · exact (link0_218 w).symm.trans (hw 3 14)
  · exact (link0_219 w).symm.trans (hw 3 15)
  · exact (link0_220 w).symm.trans (hw 3 16)
  · exact (link0_221 w).symm.trans (hw 3 17)
  · exact (link0_222 w).symm.trans (hw 3 18)
  · exact (link0_223 w).symm.trans (hw 3 19)
  · exact (link0_224 w).symm.trans (hw 3 20)
  · exact (link0_225 w).symm.trans (hw 3 21)
  · exact (link0_226 w).symm.trans (hw 3 22)
  · exact (link0_227 w).symm.trans (hw 3 23)
  · exact (link0_228 w).symm.trans (hw 3 24)
  · exact (link0_229 w).symm.trans (hw 3 25)
  · exact (link0_230 w).symm.trans (hw 3 26)
  · exact (link0_231 w).symm.trans (hw 3 27)
  · exact (link0_232 w).symm.trans (hw 3 28)
  · exact (link0_233 w).symm.trans (hw 3 29)
  · exact (link0_234 w).symm.trans (hw 3 30)
  · exact (link0_235 w).symm.trans (hw 3 31)
  · exact (link0_236 w).symm.trans (hw 3 32)
  · exact (link0_237 w).symm.trans (hw 3 33)
  · exact (link0_238 w).symm.trans (hw 3 34)
  · exact (link0_239 w).symm.trans (hw 3 35)
  · exact (link0_240 w).symm.trans (hw 3 36)
  · exact (link0_241 w).symm.trans (hw 3 37)
  · exact (link0_242 w).symm.trans (hw 3 38)
  · exact (link0_243 w).symm.trans (hw 3 39)
  · exact (link0_244 w).symm.trans (hw 3 40)
  · exact (link0_245 w).symm.trans (hw 3 41)
  · exact (link0_246 w).symm.trans (hw 3 42)
  · exact (link0_247 w).symm.trans (hw 3 43)
  · exact (link0_248 w).symm.trans (hw 3 44)
  · exact (link0_249 w).symm.trans (hw 3 45)
  · exact (link0_250 w).symm.trans (hw 3 46)
  · exact (link0_251 w).symm.trans (hw 3 47)
  · exact (link0_252 w).symm.trans (hw 3 48)
  · exact (link0_253 w).symm.trans (hw 3 49)
  · exact (link0_254 w).symm.trans (hw 3 50)
  · exact (link0_255 w).symm.trans (hw 3 51)
  · exact (link0_256 w).symm.trans (hw 3 52)
  · exact (link0_257 w).symm.trans (hw 3 53)
  · exact (link0_258 w).symm.trans (hw 3 54)
  · exact (link0_259 w).symm.trans (hw 3 55)
  · exact (link0_260 w).symm.trans (hw 3 56)
  · exact (link0_261 w).symm.trans (hw 3 57)
  · exact (link0_262 w).symm.trans (hw 3 58)
  · exact (link0_263 w).symm.trans (hw 3 59)
  · exact (link0_264 w).symm.trans (hw 3 60)
  · exact (link0_265 w).symm.trans (hw 3 61)
  · exact (link0_266 w).symm.trans (hw 3 62)
  · exact (link0_267 w).symm.trans (hw 3 63)
  · exact (link0_268 w).symm.trans (hw 3 64)
  · exact (link0_269 w).symm.trans (hw 3 65)
  · exact (link0_270 w).symm.trans (hw 3 66)
  · exact (link0_271 w).symm.trans (hw 3 67)

#print axioms kernel_case0

theorem kernel_case1 (w : Fin 264→ℂ) (hw : ∀ n i, jetBlockRow (-1) (1) n i w=0) : w=0 := by
  apply SmallLevelTwentyTwoThirdJetTriangular.kernel1 w
  intro r
  fin_cases r
  · exact (link1_0 w).symm.trans (hw 0 0)
  · exact (link1_1 w).symm.trans (hw 0 1)
  · exact (link1_2 w).symm.trans (hw 0 2)
  · exact (link1_3 w).symm.trans (hw 0 3)
  · exact (link1_4 w).symm.trans (hw 0 4)
  · exact (link1_5 w).symm.trans (hw 0 5)
  · exact (link1_6 w).symm.trans (hw 0 6)
  · exact (link1_7 w).symm.trans (hw 0 7)
  · exact (link1_8 w).symm.trans (hw 0 8)
  · exact (link1_9 w).symm.trans (hw 0 9)
  · exact (link1_10 w).symm.trans (hw 0 10)
  · exact (link1_11 w).symm.trans (hw 0 11)
  · exact (link1_12 w).symm.trans (hw 0 12)
  · exact (link1_13 w).symm.trans (hw 0 13)
  · exact (link1_14 w).symm.trans (hw 0 14)
  · exact (link1_15 w).symm.trans (hw 0 15)
  · exact (link1_16 w).symm.trans (hw 0 16)
  · exact (link1_17 w).symm.trans (hw 0 17)
  · exact (link1_18 w).symm.trans (hw 0 18)
  · exact (link1_19 w).symm.trans (hw 0 19)
  · exact (link1_20 w).symm.trans (hw 0 20)
  · exact (link1_21 w).symm.trans (hw 0 21)
  · exact (link1_22 w).symm.trans (hw 0 22)
  · exact (link1_23 w).symm.trans (hw 0 23)
  · exact (link1_24 w).symm.trans (hw 0 24)
  · exact (link1_25 w).symm.trans (hw 0 25)
  · exact (link1_26 w).symm.trans (hw 0 26)
  · exact (link1_27 w).symm.trans (hw 0 27)
  · exact (link1_28 w).symm.trans (hw 0 28)
  · exact (link1_29 w).symm.trans (hw 0 29)
  · exact (link1_30 w).symm.trans (hw 0 30)
  · exact (link1_31 w).symm.trans (hw 0 31)
  · exact (link1_32 w).symm.trans (hw 0 32)
  · exact (link1_33 w).symm.trans (hw 0 33)
  · exact (link1_34 w).symm.trans (hw 0 34)
  · exact (link1_35 w).symm.trans (hw 0 35)
  · exact (link1_36 w).symm.trans (hw 0 36)
  · exact (link1_37 w).symm.trans (hw 0 37)
  · exact (link1_38 w).symm.trans (hw 0 38)
  · exact (link1_39 w).symm.trans (hw 0 39)
  · exact (link1_40 w).symm.trans (hw 0 40)
  · exact (link1_41 w).symm.trans (hw 0 41)
  · exact (link1_42 w).symm.trans (hw 0 42)
  · exact (link1_43 w).symm.trans (hw 0 43)
  · exact (link1_44 w).symm.trans (hw 0 44)
  · exact (link1_45 w).symm.trans (hw 0 45)
  · exact (link1_46 w).symm.trans (hw 0 46)
  · exact (link1_47 w).symm.trans (hw 0 47)
  · exact (link1_48 w).symm.trans (hw 0 48)
  · exact (link1_49 w).symm.trans (hw 0 49)
  · exact (link1_50 w).symm.trans (hw 0 50)
  · exact (link1_51 w).symm.trans (hw 0 51)
  · exact (link1_52 w).symm.trans (hw 0 52)
  · exact (link1_53 w).symm.trans (hw 0 53)
  · exact (link1_54 w).symm.trans (hw 0 54)
  · exact (link1_55 w).symm.trans (hw 0 55)
  · exact (link1_56 w).symm.trans (hw 0 56)
  · exact (link1_57 w).symm.trans (hw 0 57)
  · exact (link1_58 w).symm.trans (hw 0 58)
  · exact (link1_59 w).symm.trans (hw 0 59)
  · exact (link1_60 w).symm.trans (hw 0 60)
  · exact (link1_61 w).symm.trans (hw 0 61)
  · exact (link1_62 w).symm.trans (hw 0 62)
  · exact (link1_63 w).symm.trans (hw 0 63)
  · exact (link1_64 w).symm.trans (hw 0 64)
  · exact (link1_65 w).symm.trans (hw 0 65)
  · exact (link1_66 w).symm.trans (hw 0 66)
  · exact (link1_67 w).symm.trans (hw 0 67)
  · exact (link1_68 w).symm.trans (hw 1 0)
  · exact (link1_69 w).symm.trans (hw 1 1)
  · exact (link1_70 w).symm.trans (hw 1 2)
  · exact (link1_71 w).symm.trans (hw 1 3)
  · exact (link1_72 w).symm.trans (hw 1 4)
  · exact (link1_73 w).symm.trans (hw 1 5)
  · exact (link1_74 w).symm.trans (hw 1 6)
  · exact (link1_75 w).symm.trans (hw 1 7)
  · exact (link1_76 w).symm.trans (hw 1 8)
  · exact (link1_77 w).symm.trans (hw 1 9)
  · exact (link1_78 w).symm.trans (hw 1 10)
  · exact (link1_79 w).symm.trans (hw 1 11)
  · exact (link1_80 w).symm.trans (hw 1 12)
  · exact (link1_81 w).symm.trans (hw 1 13)
  · exact (link1_82 w).symm.trans (hw 1 14)
  · exact (link1_83 w).symm.trans (hw 1 15)
  · exact (link1_84 w).symm.trans (hw 1 16)
  · exact (link1_85 w).symm.trans (hw 1 17)
  · exact (link1_86 w).symm.trans (hw 1 18)
  · exact (link1_87 w).symm.trans (hw 1 19)
  · exact (link1_88 w).symm.trans (hw 1 20)
  · exact (link1_89 w).symm.trans (hw 1 21)
  · exact (link1_90 w).symm.trans (hw 1 22)
  · exact (link1_91 w).symm.trans (hw 1 23)
  · exact (link1_92 w).symm.trans (hw 1 24)
  · exact (link1_93 w).symm.trans (hw 1 25)
  · exact (link1_94 w).symm.trans (hw 1 26)
  · exact (link1_95 w).symm.trans (hw 1 27)
  · exact (link1_96 w).symm.trans (hw 1 28)
  · exact (link1_97 w).symm.trans (hw 1 29)
  · exact (link1_98 w).symm.trans (hw 1 30)
  · exact (link1_99 w).symm.trans (hw 1 31)
  · exact (link1_100 w).symm.trans (hw 1 32)
  · exact (link1_101 w).symm.trans (hw 1 33)
  · exact (link1_102 w).symm.trans (hw 1 34)
  · exact (link1_103 w).symm.trans (hw 1 35)
  · exact (link1_104 w).symm.trans (hw 1 36)
  · exact (link1_105 w).symm.trans (hw 1 37)
  · exact (link1_106 w).symm.trans (hw 1 38)
  · exact (link1_107 w).symm.trans (hw 1 39)
  · exact (link1_108 w).symm.trans (hw 1 40)
  · exact (link1_109 w).symm.trans (hw 1 41)
  · exact (link1_110 w).symm.trans (hw 1 42)
  · exact (link1_111 w).symm.trans (hw 1 43)
  · exact (link1_112 w).symm.trans (hw 1 44)
  · exact (link1_113 w).symm.trans (hw 1 45)
  · exact (link1_114 w).symm.trans (hw 1 46)
  · exact (link1_115 w).symm.trans (hw 1 47)
  · exact (link1_116 w).symm.trans (hw 1 48)
  · exact (link1_117 w).symm.trans (hw 1 49)
  · exact (link1_118 w).symm.trans (hw 1 50)
  · exact (link1_119 w).symm.trans (hw 1 51)
  · exact (link1_120 w).symm.trans (hw 1 52)
  · exact (link1_121 w).symm.trans (hw 1 53)
  · exact (link1_122 w).symm.trans (hw 1 54)
  · exact (link1_123 w).symm.trans (hw 1 55)
  · exact (link1_124 w).symm.trans (hw 1 56)
  · exact (link1_125 w).symm.trans (hw 1 57)
  · exact (link1_126 w).symm.trans (hw 1 58)
  · exact (link1_127 w).symm.trans (hw 1 59)
  · exact (link1_128 w).symm.trans (hw 1 60)
  · exact (link1_129 w).symm.trans (hw 1 61)
  · exact (link1_130 w).symm.trans (hw 1 62)
  · exact (link1_131 w).symm.trans (hw 1 63)
  · exact (link1_132 w).symm.trans (hw 1 64)
  · exact (link1_133 w).symm.trans (hw 1 65)
  · exact (link1_134 w).symm.trans (hw 1 66)
  · exact (link1_135 w).symm.trans (hw 1 67)
  · exact (link1_136 w).symm.trans (hw 2 0)
  · exact (link1_137 w).symm.trans (hw 2 1)
  · exact (link1_138 w).symm.trans (hw 2 2)
  · exact (link1_139 w).symm.trans (hw 2 3)
  · exact (link1_140 w).symm.trans (hw 2 4)
  · exact (link1_141 w).symm.trans (hw 2 5)
  · exact (link1_142 w).symm.trans (hw 2 6)
  · exact (link1_143 w).symm.trans (hw 2 7)
  · exact (link1_144 w).symm.trans (hw 2 8)
  · exact (link1_145 w).symm.trans (hw 2 9)
  · exact (link1_146 w).symm.trans (hw 2 10)
  · exact (link1_147 w).symm.trans (hw 2 11)
  · exact (link1_148 w).symm.trans (hw 2 12)
  · exact (link1_149 w).symm.trans (hw 2 13)
  · exact (link1_150 w).symm.trans (hw 2 14)
  · exact (link1_151 w).symm.trans (hw 2 15)
  · exact (link1_152 w).symm.trans (hw 2 16)
  · exact (link1_153 w).symm.trans (hw 2 17)
  · exact (link1_154 w).symm.trans (hw 2 18)
  · exact (link1_155 w).symm.trans (hw 2 19)
  · exact (link1_156 w).symm.trans (hw 2 20)
  · exact (link1_157 w).symm.trans (hw 2 21)
  · exact (link1_158 w).symm.trans (hw 2 22)
  · exact (link1_159 w).symm.trans (hw 2 23)
  · exact (link1_160 w).symm.trans (hw 2 24)
  · exact (link1_161 w).symm.trans (hw 2 25)
  · exact (link1_162 w).symm.trans (hw 2 26)
  · exact (link1_163 w).symm.trans (hw 2 27)
  · exact (link1_164 w).symm.trans (hw 2 28)
  · exact (link1_165 w).symm.trans (hw 2 29)
  · exact (link1_166 w).symm.trans (hw 2 30)
  · exact (link1_167 w).symm.trans (hw 2 31)
  · exact (link1_168 w).symm.trans (hw 2 32)
  · exact (link1_169 w).symm.trans (hw 2 33)
  · exact (link1_170 w).symm.trans (hw 2 34)
  · exact (link1_171 w).symm.trans (hw 2 35)
  · exact (link1_172 w).symm.trans (hw 2 36)
  · exact (link1_173 w).symm.trans (hw 2 37)
  · exact (link1_174 w).symm.trans (hw 2 38)
  · exact (link1_175 w).symm.trans (hw 2 39)
  · exact (link1_176 w).symm.trans (hw 2 40)
  · exact (link1_177 w).symm.trans (hw 2 41)
  · exact (link1_178 w).symm.trans (hw 2 42)
  · exact (link1_179 w).symm.trans (hw 2 43)
  · exact (link1_180 w).symm.trans (hw 2 44)
  · exact (link1_181 w).symm.trans (hw 2 45)
  · exact (link1_182 w).symm.trans (hw 2 46)
  · exact (link1_183 w).symm.trans (hw 2 47)
  · exact (link1_184 w).symm.trans (hw 2 48)
  · exact (link1_185 w).symm.trans (hw 2 49)
  · exact (link1_186 w).symm.trans (hw 2 50)
  · exact (link1_187 w).symm.trans (hw 2 51)
  · exact (link1_188 w).symm.trans (hw 2 52)
  · exact (link1_189 w).symm.trans (hw 2 53)
  · exact (link1_190 w).symm.trans (hw 2 54)
  · exact (link1_191 w).symm.trans (hw 2 55)
  · exact (link1_192 w).symm.trans (hw 2 56)
  · exact (link1_193 w).symm.trans (hw 2 57)
  · exact (link1_194 w).symm.trans (hw 2 58)
  · exact (link1_195 w).symm.trans (hw 2 59)
  · exact (link1_196 w).symm.trans (hw 2 60)
  · exact (link1_197 w).symm.trans (hw 2 61)
  · exact (link1_198 w).symm.trans (hw 2 62)
  · exact (link1_199 w).symm.trans (hw 2 63)
  · exact (link1_200 w).symm.trans (hw 2 64)
  · exact (link1_201 w).symm.trans (hw 2 65)
  · exact (link1_202 w).symm.trans (hw 2 66)
  · exact (link1_203 w).symm.trans (hw 2 67)
  · exact (link1_204 w).symm.trans (hw 3 0)
  · exact (link1_205 w).symm.trans (hw 3 1)
  · exact (link1_206 w).symm.trans (hw 3 2)
  · exact (link1_207 w).symm.trans (hw 3 3)
  · exact (link1_208 w).symm.trans (hw 3 4)
  · exact (link1_209 w).symm.trans (hw 3 5)
  · exact (link1_210 w).symm.trans (hw 3 6)
  · exact (link1_211 w).symm.trans (hw 3 7)
  · exact (link1_212 w).symm.trans (hw 3 8)
  · exact (link1_213 w).symm.trans (hw 3 9)
  · exact (link1_214 w).symm.trans (hw 3 10)
  · exact (link1_215 w).symm.trans (hw 3 11)
  · exact (link1_216 w).symm.trans (hw 3 12)
  · exact (link1_217 w).symm.trans (hw 3 13)
  · exact (link1_218 w).symm.trans (hw 3 14)
  · exact (link1_219 w).symm.trans (hw 3 15)
  · exact (link1_220 w).symm.trans (hw 3 16)
  · exact (link1_221 w).symm.trans (hw 3 17)
  · exact (link1_222 w).symm.trans (hw 3 18)
  · exact (link1_223 w).symm.trans (hw 3 19)
  · exact (link1_224 w).symm.trans (hw 3 20)
  · exact (link1_225 w).symm.trans (hw 3 21)
  · exact (link1_226 w).symm.trans (hw 3 22)
  · exact (link1_227 w).symm.trans (hw 3 23)
  · exact (link1_228 w).symm.trans (hw 3 24)
  · exact (link1_229 w).symm.trans (hw 3 25)
  · exact (link1_230 w).symm.trans (hw 3 26)
  · exact (link1_231 w).symm.trans (hw 3 27)
  · exact (link1_232 w).symm.trans (hw 3 28)
  · exact (link1_233 w).symm.trans (hw 3 29)
  · exact (link1_234 w).symm.trans (hw 3 30)
  · exact (link1_235 w).symm.trans (hw 3 31)
  · exact (link1_236 w).symm.trans (hw 3 32)
  · exact (link1_237 w).symm.trans (hw 3 33)
  · exact (link1_238 w).symm.trans (hw 3 34)
  · exact (link1_239 w).symm.trans (hw 3 35)
  · exact (link1_240 w).symm.trans (hw 3 36)
  · exact (link1_241 w).symm.trans (hw 3 37)
  · exact (link1_242 w).symm.trans (hw 3 38)
  · exact (link1_243 w).symm.trans (hw 3 39)
  · exact (link1_244 w).symm.trans (hw 3 40)
  · exact (link1_245 w).symm.trans (hw 3 41)
  · exact (link1_246 w).symm.trans (hw 3 42)
  · exact (link1_247 w).symm.trans (hw 3 43)
  · exact (link1_248 w).symm.trans (hw 3 44)
  · exact (link1_249 w).symm.trans (hw 3 45)
  · exact (link1_250 w).symm.trans (hw 3 46)
  · exact (link1_251 w).symm.trans (hw 3 47)
  · exact (link1_252 w).symm.trans (hw 3 48)
  · exact (link1_253 w).symm.trans (hw 3 49)
  · exact (link1_254 w).symm.trans (hw 3 50)
  · exact (link1_255 w).symm.trans (hw 3 51)
  · exact (link1_256 w).symm.trans (hw 3 52)
  · exact (link1_257 w).symm.trans (hw 3 53)
  · exact (link1_258 w).symm.trans (hw 3 54)
  · exact (link1_259 w).symm.trans (hw 3 55)
  · exact (link1_260 w).symm.trans (hw 3 56)
  · exact (link1_261 w).symm.trans (hw 3 57)
  · exact (link1_262 w).symm.trans (hw 3 58)
  · exact (link1_263 w).symm.trans (hw 3 59)
  · exact (link1_264 w).symm.trans (hw 3 60)
  · exact (link1_265 w).symm.trans (hw 3 61)
  · exact (link1_266 w).symm.trans (hw 3 62)
  · exact (link1_267 w).symm.trans (hw 3 63)
  · exact (link1_268 w).symm.trans (hw 3 64)
  · exact (link1_269 w).symm.trans (hw 3 65)
  · exact (link1_270 w).symm.trans (hw 3 66)
  · exact (link1_271 w).symm.trans (hw 3 67)

#print axioms kernel_case1

theorem kernel_case2 (w : Fin 264→ℂ) (hw : ∀ n i, jetBlockRow (1) (-1) n i w=0) : w=0 := by
  apply SmallLevelTwentyTwoThirdJetTriangular.kernel2 w
  intro r
  fin_cases r
  · exact (link2_0 w).symm.trans (hw 0 0)
  · exact (link2_1 w).symm.trans (hw 0 1)
  · exact (link2_2 w).symm.trans (hw 0 2)
  · exact (link2_3 w).symm.trans (hw 0 3)
  · exact (link2_4 w).symm.trans (hw 0 4)
  · exact (link2_5 w).symm.trans (hw 0 5)
  · exact (link2_6 w).symm.trans (hw 0 6)
  · exact (link2_7 w).symm.trans (hw 0 7)
  · exact (link2_8 w).symm.trans (hw 0 8)
  · exact (link2_9 w).symm.trans (hw 0 9)
  · exact (link2_10 w).symm.trans (hw 0 10)
  · exact (link2_11 w).symm.trans (hw 0 11)
  · exact (link2_12 w).symm.trans (hw 0 12)
  · exact (link2_13 w).symm.trans (hw 0 13)
  · exact (link2_14 w).symm.trans (hw 0 14)
  · exact (link2_15 w).symm.trans (hw 0 15)
  · exact (link2_16 w).symm.trans (hw 0 16)
  · exact (link2_17 w).symm.trans (hw 0 17)
  · exact (link2_18 w).symm.trans (hw 0 18)
  · exact (link2_19 w).symm.trans (hw 0 19)
  · exact (link2_20 w).symm.trans (hw 0 20)
  · exact (link2_21 w).symm.trans (hw 0 21)
  · exact (link2_22 w).symm.trans (hw 0 22)
  · exact (link2_23 w).symm.trans (hw 0 23)
  · exact (link2_24 w).symm.trans (hw 0 24)
  · exact (link2_25 w).symm.trans (hw 0 25)
  · exact (link2_26 w).symm.trans (hw 0 26)
  · exact (link2_27 w).symm.trans (hw 0 27)
  · exact (link2_28 w).symm.trans (hw 0 28)
  · exact (link2_29 w).symm.trans (hw 0 29)
  · exact (link2_30 w).symm.trans (hw 0 30)
  · exact (link2_31 w).symm.trans (hw 0 31)
  · exact (link2_32 w).symm.trans (hw 0 32)
  · exact (link2_33 w).symm.trans (hw 0 33)
  · exact (link2_34 w).symm.trans (hw 0 34)
  · exact (link2_35 w).symm.trans (hw 0 35)
  · exact (link2_36 w).symm.trans (hw 0 36)
  · exact (link2_37 w).symm.trans (hw 0 37)
  · exact (link2_38 w).symm.trans (hw 0 38)
  · exact (link2_39 w).symm.trans (hw 0 39)
  · exact (link2_40 w).symm.trans (hw 0 40)
  · exact (link2_41 w).symm.trans (hw 0 41)
  · exact (link2_42 w).symm.trans (hw 0 42)
  · exact (link2_43 w).symm.trans (hw 0 43)
  · exact (link2_44 w).symm.trans (hw 0 44)
  · exact (link2_45 w).symm.trans (hw 0 45)
  · exact (link2_46 w).symm.trans (hw 0 46)
  · exact (link2_47 w).symm.trans (hw 0 47)
  · exact (link2_48 w).symm.trans (hw 0 48)
  · exact (link2_49 w).symm.trans (hw 0 49)
  · exact (link2_50 w).symm.trans (hw 0 50)
  · exact (link2_51 w).symm.trans (hw 0 51)
  · exact (link2_52 w).symm.trans (hw 0 52)
  · exact (link2_53 w).symm.trans (hw 0 53)
  · exact (link2_54 w).symm.trans (hw 0 54)
  · exact (link2_55 w).symm.trans (hw 0 55)
  · exact (link2_56 w).symm.trans (hw 0 56)
  · exact (link2_57 w).symm.trans (hw 0 57)
  · exact (link2_58 w).symm.trans (hw 0 58)
  · exact (link2_59 w).symm.trans (hw 0 59)
  · exact (link2_60 w).symm.trans (hw 0 60)
  · exact (link2_61 w).symm.trans (hw 0 61)
  · exact (link2_62 w).symm.trans (hw 0 62)
  · exact (link2_63 w).symm.trans (hw 0 63)
  · exact (link2_64 w).symm.trans (hw 0 64)
  · exact (link2_65 w).symm.trans (hw 0 65)
  · exact (link2_66 w).symm.trans (hw 0 66)
  · exact (link2_67 w).symm.trans (hw 0 67)
  · exact (link2_68 w).symm.trans (hw 1 0)
  · exact (link2_69 w).symm.trans (hw 1 1)
  · exact (link2_70 w).symm.trans (hw 1 2)
  · exact (link2_71 w).symm.trans (hw 1 3)
  · exact (link2_72 w).symm.trans (hw 1 4)
  · exact (link2_73 w).symm.trans (hw 1 5)
  · exact (link2_74 w).symm.trans (hw 1 6)
  · exact (link2_75 w).symm.trans (hw 1 7)
  · exact (link2_76 w).symm.trans (hw 1 8)
  · exact (link2_77 w).symm.trans (hw 1 9)
  · exact (link2_78 w).symm.trans (hw 1 10)
  · exact (link2_79 w).symm.trans (hw 1 11)
  · exact (link2_80 w).symm.trans (hw 1 12)
  · exact (link2_81 w).symm.trans (hw 1 13)
  · exact (link2_82 w).symm.trans (hw 1 14)
  · exact (link2_83 w).symm.trans (hw 1 15)
  · exact (link2_84 w).symm.trans (hw 1 16)
  · exact (link2_85 w).symm.trans (hw 1 17)
  · exact (link2_86 w).symm.trans (hw 1 18)
  · exact (link2_87 w).symm.trans (hw 1 19)
  · exact (link2_88 w).symm.trans (hw 1 20)
  · exact (link2_89 w).symm.trans (hw 1 21)
  · exact (link2_90 w).symm.trans (hw 1 22)
  · exact (link2_91 w).symm.trans (hw 1 23)
  · exact (link2_92 w).symm.trans (hw 1 24)
  · exact (link2_93 w).symm.trans (hw 1 25)
  · exact (link2_94 w).symm.trans (hw 1 26)
  · exact (link2_95 w).symm.trans (hw 1 27)
  · exact (link2_96 w).symm.trans (hw 1 28)
  · exact (link2_97 w).symm.trans (hw 1 29)
  · exact (link2_98 w).symm.trans (hw 1 30)
  · exact (link2_99 w).symm.trans (hw 1 31)
  · exact (link2_100 w).symm.trans (hw 1 32)
  · exact (link2_101 w).symm.trans (hw 1 33)
  · exact (link2_102 w).symm.trans (hw 1 34)
  · exact (link2_103 w).symm.trans (hw 1 35)
  · exact (link2_104 w).symm.trans (hw 1 36)
  · exact (link2_105 w).symm.trans (hw 1 37)
  · exact (link2_106 w).symm.trans (hw 1 38)
  · exact (link2_107 w).symm.trans (hw 1 39)
  · exact (link2_108 w).symm.trans (hw 1 40)
  · exact (link2_109 w).symm.trans (hw 1 41)
  · exact (link2_110 w).symm.trans (hw 1 42)
  · exact (link2_111 w).symm.trans (hw 1 43)
  · exact (link2_112 w).symm.trans (hw 1 44)
  · exact (link2_113 w).symm.trans (hw 1 45)
  · exact (link2_114 w).symm.trans (hw 1 46)
  · exact (link2_115 w).symm.trans (hw 1 47)
  · exact (link2_116 w).symm.trans (hw 1 48)
  · exact (link2_117 w).symm.trans (hw 1 49)
  · exact (link2_118 w).symm.trans (hw 1 50)
  · exact (link2_119 w).symm.trans (hw 1 51)
  · exact (link2_120 w).symm.trans (hw 1 52)
  · exact (link2_121 w).symm.trans (hw 1 53)
  · exact (link2_122 w).symm.trans (hw 1 54)
  · exact (link2_123 w).symm.trans (hw 1 55)
  · exact (link2_124 w).symm.trans (hw 1 56)
  · exact (link2_125 w).symm.trans (hw 1 57)
  · exact (link2_126 w).symm.trans (hw 1 58)
  · exact (link2_127 w).symm.trans (hw 1 59)
  · exact (link2_128 w).symm.trans (hw 1 60)
  · exact (link2_129 w).symm.trans (hw 1 61)
  · exact (link2_130 w).symm.trans (hw 1 62)
  · exact (link2_131 w).symm.trans (hw 1 63)
  · exact (link2_132 w).symm.trans (hw 1 64)
  · exact (link2_133 w).symm.trans (hw 1 65)
  · exact (link2_134 w).symm.trans (hw 1 66)
  · exact (link2_135 w).symm.trans (hw 1 67)
  · exact (link2_136 w).symm.trans (hw 2 0)
  · exact (link2_137 w).symm.trans (hw 2 1)
  · exact (link2_138 w).symm.trans (hw 2 2)
  · exact (link2_139 w).symm.trans (hw 2 3)
  · exact (link2_140 w).symm.trans (hw 2 4)
  · exact (link2_141 w).symm.trans (hw 2 5)
  · exact (link2_142 w).symm.trans (hw 2 6)
  · exact (link2_143 w).symm.trans (hw 2 7)
  · exact (link2_144 w).symm.trans (hw 2 8)
  · exact (link2_145 w).symm.trans (hw 2 9)
  · exact (link2_146 w).symm.trans (hw 2 10)
  · exact (link2_147 w).symm.trans (hw 2 11)
  · exact (link2_148 w).symm.trans (hw 2 12)
  · exact (link2_149 w).symm.trans (hw 2 13)
  · exact (link2_150 w).symm.trans (hw 2 14)
  · exact (link2_151 w).symm.trans (hw 2 15)
  · exact (link2_152 w).symm.trans (hw 2 16)
  · exact (link2_153 w).symm.trans (hw 2 17)
  · exact (link2_154 w).symm.trans (hw 2 18)
  · exact (link2_155 w).symm.trans (hw 2 19)
  · exact (link2_156 w).symm.trans (hw 2 20)
  · exact (link2_157 w).symm.trans (hw 2 21)
  · exact (link2_158 w).symm.trans (hw 2 22)
  · exact (link2_159 w).symm.trans (hw 2 23)
  · exact (link2_160 w).symm.trans (hw 2 24)
  · exact (link2_161 w).symm.trans (hw 2 25)
  · exact (link2_162 w).symm.trans (hw 2 26)
  · exact (link2_163 w).symm.trans (hw 2 27)
  · exact (link2_164 w).symm.trans (hw 2 28)
  · exact (link2_165 w).symm.trans (hw 2 29)
  · exact (link2_166 w).symm.trans (hw 2 30)
  · exact (link2_167 w).symm.trans (hw 2 31)
  · exact (link2_168 w).symm.trans (hw 2 32)
  · exact (link2_169 w).symm.trans (hw 2 33)
  · exact (link2_170 w).symm.trans (hw 2 34)
  · exact (link2_171 w).symm.trans (hw 2 35)
  · exact (link2_172 w).symm.trans (hw 2 36)
  · exact (link2_173 w).symm.trans (hw 2 37)
  · exact (link2_174 w).symm.trans (hw 2 38)
  · exact (link2_175 w).symm.trans (hw 2 39)
  · exact (link2_176 w).symm.trans (hw 2 40)
  · exact (link2_177 w).symm.trans (hw 2 41)
  · exact (link2_178 w).symm.trans (hw 2 42)
  · exact (link2_179 w).symm.trans (hw 2 43)
  · exact (link2_180 w).symm.trans (hw 2 44)
  · exact (link2_181 w).symm.trans (hw 2 45)
  · exact (link2_182 w).symm.trans (hw 2 46)
  · exact (link2_183 w).symm.trans (hw 2 47)
  · exact (link2_184 w).symm.trans (hw 2 48)
  · exact (link2_185 w).symm.trans (hw 2 49)
  · exact (link2_186 w).symm.trans (hw 2 50)
  · exact (link2_187 w).symm.trans (hw 2 51)
  · exact (link2_188 w).symm.trans (hw 2 52)
  · exact (link2_189 w).symm.trans (hw 2 53)
  · exact (link2_190 w).symm.trans (hw 2 54)
  · exact (link2_191 w).symm.trans (hw 2 55)
  · exact (link2_192 w).symm.trans (hw 2 56)
  · exact (link2_193 w).symm.trans (hw 2 57)
  · exact (link2_194 w).symm.trans (hw 2 58)
  · exact (link2_195 w).symm.trans (hw 2 59)
  · exact (link2_196 w).symm.trans (hw 2 60)
  · exact (link2_197 w).symm.trans (hw 2 61)
  · exact (link2_198 w).symm.trans (hw 2 62)
  · exact (link2_199 w).symm.trans (hw 2 63)
  · exact (link2_200 w).symm.trans (hw 2 64)
  · exact (link2_201 w).symm.trans (hw 2 65)
  · exact (link2_202 w).symm.trans (hw 2 66)
  · exact (link2_203 w).symm.trans (hw 2 67)
  · exact (link2_204 w).symm.trans (hw 3 0)
  · exact (link2_205 w).symm.trans (hw 3 1)
  · exact (link2_206 w).symm.trans (hw 3 2)
  · exact (link2_207 w).symm.trans (hw 3 3)
  · exact (link2_208 w).symm.trans (hw 3 4)
  · exact (link2_209 w).symm.trans (hw 3 5)
  · exact (link2_210 w).symm.trans (hw 3 6)
  · exact (link2_211 w).symm.trans (hw 3 7)
  · exact (link2_212 w).symm.trans (hw 3 8)
  · exact (link2_213 w).symm.trans (hw 3 9)
  · exact (link2_214 w).symm.trans (hw 3 10)
  · exact (link2_215 w).symm.trans (hw 3 11)
  · exact (link2_216 w).symm.trans (hw 3 12)
  · exact (link2_217 w).symm.trans (hw 3 13)
  · exact (link2_218 w).symm.trans (hw 3 14)
  · exact (link2_219 w).symm.trans (hw 3 15)
  · exact (link2_220 w).symm.trans (hw 3 16)
  · exact (link2_221 w).symm.trans (hw 3 17)
  · exact (link2_222 w).symm.trans (hw 3 18)
  · exact (link2_223 w).symm.trans (hw 3 19)
  · exact (link2_224 w).symm.trans (hw 3 20)
  · exact (link2_225 w).symm.trans (hw 3 21)
  · exact (link2_226 w).symm.trans (hw 3 22)
  · exact (link2_227 w).symm.trans (hw 3 23)
  · exact (link2_228 w).symm.trans (hw 3 24)
  · exact (link2_229 w).symm.trans (hw 3 25)
  · exact (link2_230 w).symm.trans (hw 3 26)
  · exact (link2_231 w).symm.trans (hw 3 27)
  · exact (link2_232 w).symm.trans (hw 3 28)
  · exact (link2_233 w).symm.trans (hw 3 29)
  · exact (link2_234 w).symm.trans (hw 3 30)
  · exact (link2_235 w).symm.trans (hw 3 31)
  · exact (link2_236 w).symm.trans (hw 3 32)
  · exact (link2_237 w).symm.trans (hw 3 33)
  · exact (link2_238 w).symm.trans (hw 3 34)
  · exact (link2_239 w).symm.trans (hw 3 35)
  · exact (link2_240 w).symm.trans (hw 3 36)
  · exact (link2_241 w).symm.trans (hw 3 37)
  · exact (link2_242 w).symm.trans (hw 3 38)
  · exact (link2_243 w).symm.trans (hw 3 39)
  · exact (link2_244 w).symm.trans (hw 3 40)
  · exact (link2_245 w).symm.trans (hw 3 41)
  · exact (link2_246 w).symm.trans (hw 3 42)
  · exact (link2_247 w).symm.trans (hw 3 43)
  · exact (link2_248 w).symm.trans (hw 3 44)
  · exact (link2_249 w).symm.trans (hw 3 45)
  · exact (link2_250 w).symm.trans (hw 3 46)
  · exact (link2_251 w).symm.trans (hw 3 47)
  · exact (link2_252 w).symm.trans (hw 3 48)
  · exact (link2_253 w).symm.trans (hw 3 49)
  · exact (link2_254 w).symm.trans (hw 3 50)
  · exact (link2_255 w).symm.trans (hw 3 51)
  · exact (link2_256 w).symm.trans (hw 3 52)
  · exact (link2_257 w).symm.trans (hw 3 53)
  · exact (link2_258 w).symm.trans (hw 3 54)
  · exact (link2_259 w).symm.trans (hw 3 55)
  · exact (link2_260 w).symm.trans (hw 3 56)
  · exact (link2_261 w).symm.trans (hw 3 57)
  · exact (link2_262 w).symm.trans (hw 3 58)
  · exact (link2_263 w).symm.trans (hw 3 59)
  · exact (link2_264 w).symm.trans (hw 3 60)
  · exact (link2_265 w).symm.trans (hw 3 61)
  · exact (link2_266 w).symm.trans (hw 3 62)
  · exact (link2_267 w).symm.trans (hw 3 63)
  · exact (link2_268 w).symm.trans (hw 3 64)
  · exact (link2_269 w).symm.trans (hw 3 65)
  · exact (link2_270 w).symm.trans (hw 3 66)
  · exact (link2_271 w).symm.trans (hw 3 67)

#print axioms kernel_case2

theorem kernel_case3 (w : Fin 264→ℂ) (hw : ∀ n i, jetBlockRow (1) (1) n i w=0) : w=0 := by
  apply SmallLevelTwentyTwoThirdJetTriangular.kernel3 w
  intro r
  fin_cases r
  · exact (link3_0 w).symm.trans (hw 0 0)
  · exact (link3_1 w).symm.trans (hw 0 1)
  · exact (link3_2 w).symm.trans (hw 0 2)
  · exact (link3_3 w).symm.trans (hw 0 3)
  · exact (link3_4 w).symm.trans (hw 0 4)
  · exact (link3_5 w).symm.trans (hw 0 5)
  · exact (link3_6 w).symm.trans (hw 0 6)
  · exact (link3_7 w).symm.trans (hw 0 7)
  · exact (link3_8 w).symm.trans (hw 0 8)
  · exact (link3_9 w).symm.trans (hw 0 9)
  · exact (link3_10 w).symm.trans (hw 0 10)
  · exact (link3_11 w).symm.trans (hw 0 11)
  · exact (link3_12 w).symm.trans (hw 0 12)
  · exact (link3_13 w).symm.trans (hw 0 13)
  · exact (link3_14 w).symm.trans (hw 0 14)
  · exact (link3_15 w).symm.trans (hw 0 15)
  · exact (link3_16 w).symm.trans (hw 0 16)
  · exact (link3_17 w).symm.trans (hw 0 17)
  · exact (link3_18 w).symm.trans (hw 0 18)
  · exact (link3_19 w).symm.trans (hw 0 19)
  · exact (link3_20 w).symm.trans (hw 0 20)
  · exact (link3_21 w).symm.trans (hw 0 21)
  · exact (link3_22 w).symm.trans (hw 0 22)
  · exact (link3_23 w).symm.trans (hw 0 23)
  · exact (link3_24 w).symm.trans (hw 0 24)
  · exact (link3_25 w).symm.trans (hw 0 25)
  · exact (link3_26 w).symm.trans (hw 0 26)
  · exact (link3_27 w).symm.trans (hw 0 27)
  · exact (link3_28 w).symm.trans (hw 0 28)
  · exact (link3_29 w).symm.trans (hw 0 29)
  · exact (link3_30 w).symm.trans (hw 0 30)
  · exact (link3_31 w).symm.trans (hw 0 31)
  · exact (link3_32 w).symm.trans (hw 0 32)
  · exact (link3_33 w).symm.trans (hw 0 33)
  · exact (link3_34 w).symm.trans (hw 0 34)
  · exact (link3_35 w).symm.trans (hw 0 35)
  · exact (link3_36 w).symm.trans (hw 0 36)
  · exact (link3_37 w).symm.trans (hw 0 37)
  · exact (link3_38 w).symm.trans (hw 0 38)
  · exact (link3_39 w).symm.trans (hw 0 39)
  · exact (link3_40 w).symm.trans (hw 0 40)
  · exact (link3_41 w).symm.trans (hw 0 41)
  · exact (link3_42 w).symm.trans (hw 0 42)
  · exact (link3_43 w).symm.trans (hw 0 43)
  · exact (link3_44 w).symm.trans (hw 0 44)
  · exact (link3_45 w).symm.trans (hw 0 45)
  · exact (link3_46 w).symm.trans (hw 0 46)
  · exact (link3_47 w).symm.trans (hw 0 47)
  · exact (link3_48 w).symm.trans (hw 0 48)
  · exact (link3_49 w).symm.trans (hw 0 49)
  · exact (link3_50 w).symm.trans (hw 0 50)
  · exact (link3_51 w).symm.trans (hw 0 51)
  · exact (link3_52 w).symm.trans (hw 0 52)
  · exact (link3_53 w).symm.trans (hw 0 53)
  · exact (link3_54 w).symm.trans (hw 0 54)
  · exact (link3_55 w).symm.trans (hw 0 55)
  · exact (link3_56 w).symm.trans (hw 0 56)
  · exact (link3_57 w).symm.trans (hw 0 57)
  · exact (link3_58 w).symm.trans (hw 0 58)
  · exact (link3_59 w).symm.trans (hw 0 59)
  · exact (link3_60 w).symm.trans (hw 0 60)
  · exact (link3_61 w).symm.trans (hw 0 61)
  · exact (link3_62 w).symm.trans (hw 0 62)
  · exact (link3_63 w).symm.trans (hw 0 63)
  · exact (link3_64 w).symm.trans (hw 0 64)
  · exact (link3_65 w).symm.trans (hw 0 65)
  · exact (link3_66 w).symm.trans (hw 0 66)
  · exact (link3_67 w).symm.trans (hw 0 67)
  · exact (link3_68 w).symm.trans (hw 1 0)
  · exact (link3_69 w).symm.trans (hw 1 1)
  · exact (link3_70 w).symm.trans (hw 1 2)
  · exact (link3_71 w).symm.trans (hw 1 3)
  · exact (link3_72 w).symm.trans (hw 1 4)
  · exact (link3_73 w).symm.trans (hw 1 5)
  · exact (link3_74 w).symm.trans (hw 1 6)
  · exact (link3_75 w).symm.trans (hw 1 7)
  · exact (link3_76 w).symm.trans (hw 1 8)
  · exact (link3_77 w).symm.trans (hw 1 9)
  · exact (link3_78 w).symm.trans (hw 1 10)
  · exact (link3_79 w).symm.trans (hw 1 11)
  · exact (link3_80 w).symm.trans (hw 1 12)
  · exact (link3_81 w).symm.trans (hw 1 13)
  · exact (link3_82 w).symm.trans (hw 1 14)
  · exact (link3_83 w).symm.trans (hw 1 15)
  · exact (link3_84 w).symm.trans (hw 1 16)
  · exact (link3_85 w).symm.trans (hw 1 17)
  · exact (link3_86 w).symm.trans (hw 1 18)
  · exact (link3_87 w).symm.trans (hw 1 19)
  · exact (link3_88 w).symm.trans (hw 1 20)
  · exact (link3_89 w).symm.trans (hw 1 21)
  · exact (link3_90 w).symm.trans (hw 1 22)
  · exact (link3_91 w).symm.trans (hw 1 23)
  · exact (link3_92 w).symm.trans (hw 1 24)
  · exact (link3_93 w).symm.trans (hw 1 25)
  · exact (link3_94 w).symm.trans (hw 1 26)
  · exact (link3_95 w).symm.trans (hw 1 27)
  · exact (link3_96 w).symm.trans (hw 1 28)
  · exact (link3_97 w).symm.trans (hw 1 29)
  · exact (link3_98 w).symm.trans (hw 1 30)
  · exact (link3_99 w).symm.trans (hw 1 31)
  · exact (link3_100 w).symm.trans (hw 1 32)
  · exact (link3_101 w).symm.trans (hw 1 33)
  · exact (link3_102 w).symm.trans (hw 1 34)
  · exact (link3_103 w).symm.trans (hw 1 35)
  · exact (link3_104 w).symm.trans (hw 1 36)
  · exact (link3_105 w).symm.trans (hw 1 37)
  · exact (link3_106 w).symm.trans (hw 1 38)
  · exact (link3_107 w).symm.trans (hw 1 39)
  · exact (link3_108 w).symm.trans (hw 1 40)
  · exact (link3_109 w).symm.trans (hw 1 41)
  · exact (link3_110 w).symm.trans (hw 1 42)
  · exact (link3_111 w).symm.trans (hw 1 43)
  · exact (link3_112 w).symm.trans (hw 1 44)
  · exact (link3_113 w).symm.trans (hw 1 45)
  · exact (link3_114 w).symm.trans (hw 1 46)
  · exact (link3_115 w).symm.trans (hw 1 47)
  · exact (link3_116 w).symm.trans (hw 1 48)
  · exact (link3_117 w).symm.trans (hw 1 49)
  · exact (link3_118 w).symm.trans (hw 1 50)
  · exact (link3_119 w).symm.trans (hw 1 51)
  · exact (link3_120 w).symm.trans (hw 1 52)
  · exact (link3_121 w).symm.trans (hw 1 53)
  · exact (link3_122 w).symm.trans (hw 1 54)
  · exact (link3_123 w).symm.trans (hw 1 55)
  · exact (link3_124 w).symm.trans (hw 1 56)
  · exact (link3_125 w).symm.trans (hw 1 57)
  · exact (link3_126 w).symm.trans (hw 1 58)
  · exact (link3_127 w).symm.trans (hw 1 59)
  · exact (link3_128 w).symm.trans (hw 1 60)
  · exact (link3_129 w).symm.trans (hw 1 61)
  · exact (link3_130 w).symm.trans (hw 1 62)
  · exact (link3_131 w).symm.trans (hw 1 63)
  · exact (link3_132 w).symm.trans (hw 1 64)
  · exact (link3_133 w).symm.trans (hw 1 65)
  · exact (link3_134 w).symm.trans (hw 1 66)
  · exact (link3_135 w).symm.trans (hw 1 67)
  · exact (link3_136 w).symm.trans (hw 2 0)
  · exact (link3_137 w).symm.trans (hw 2 1)
  · exact (link3_138 w).symm.trans (hw 2 2)
  · exact (link3_139 w).symm.trans (hw 2 3)
  · exact (link3_140 w).symm.trans (hw 2 4)
  · exact (link3_141 w).symm.trans (hw 2 5)
  · exact (link3_142 w).symm.trans (hw 2 6)
  · exact (link3_143 w).symm.trans (hw 2 7)
  · exact (link3_144 w).symm.trans (hw 2 8)
  · exact (link3_145 w).symm.trans (hw 2 9)
  · exact (link3_146 w).symm.trans (hw 2 10)
  · exact (link3_147 w).symm.trans (hw 2 11)
  · exact (link3_148 w).symm.trans (hw 2 12)
  · exact (link3_149 w).symm.trans (hw 2 13)
  · exact (link3_150 w).symm.trans (hw 2 14)
  · exact (link3_151 w).symm.trans (hw 2 15)
  · exact (link3_152 w).symm.trans (hw 2 16)
  · exact (link3_153 w).symm.trans (hw 2 17)
  · exact (link3_154 w).symm.trans (hw 2 18)
  · exact (link3_155 w).symm.trans (hw 2 19)
  · exact (link3_156 w).symm.trans (hw 2 20)
  · exact (link3_157 w).symm.trans (hw 2 21)
  · exact (link3_158 w).symm.trans (hw 2 22)
  · exact (link3_159 w).symm.trans (hw 2 23)
  · exact (link3_160 w).symm.trans (hw 2 24)
  · exact (link3_161 w).symm.trans (hw 2 25)
  · exact (link3_162 w).symm.trans (hw 2 26)
  · exact (link3_163 w).symm.trans (hw 2 27)
  · exact (link3_164 w).symm.trans (hw 2 28)
  · exact (link3_165 w).symm.trans (hw 2 29)
  · exact (link3_166 w).symm.trans (hw 2 30)
  · exact (link3_167 w).symm.trans (hw 2 31)
  · exact (link3_168 w).symm.trans (hw 2 32)
  · exact (link3_169 w).symm.trans (hw 2 33)
  · exact (link3_170 w).symm.trans (hw 2 34)
  · exact (link3_171 w).symm.trans (hw 2 35)
  · exact (link3_172 w).symm.trans (hw 2 36)
  · exact (link3_173 w).symm.trans (hw 2 37)
  · exact (link3_174 w).symm.trans (hw 2 38)
  · exact (link3_175 w).symm.trans (hw 2 39)
  · exact (link3_176 w).symm.trans (hw 2 40)
  · exact (link3_177 w).symm.trans (hw 2 41)
  · exact (link3_178 w).symm.trans (hw 2 42)
  · exact (link3_179 w).symm.trans (hw 2 43)
  · exact (link3_180 w).symm.trans (hw 2 44)
  · exact (link3_181 w).symm.trans (hw 2 45)
  · exact (link3_182 w).symm.trans (hw 2 46)
  · exact (link3_183 w).symm.trans (hw 2 47)
  · exact (link3_184 w).symm.trans (hw 2 48)
  · exact (link3_185 w).symm.trans (hw 2 49)
  · exact (link3_186 w).symm.trans (hw 2 50)
  · exact (link3_187 w).symm.trans (hw 2 51)
  · exact (link3_188 w).symm.trans (hw 2 52)
  · exact (link3_189 w).symm.trans (hw 2 53)
  · exact (link3_190 w).symm.trans (hw 2 54)
  · exact (link3_191 w).symm.trans (hw 2 55)
  · exact (link3_192 w).symm.trans (hw 2 56)
  · exact (link3_193 w).symm.trans (hw 2 57)
  · exact (link3_194 w).symm.trans (hw 2 58)
  · exact (link3_195 w).symm.trans (hw 2 59)
  · exact (link3_196 w).symm.trans (hw 2 60)
  · exact (link3_197 w).symm.trans (hw 2 61)
  · exact (link3_198 w).symm.trans (hw 2 62)
  · exact (link3_199 w).symm.trans (hw 2 63)
  · exact (link3_200 w).symm.trans (hw 2 64)
  · exact (link3_201 w).symm.trans (hw 2 65)
  · exact (link3_202 w).symm.trans (hw 2 66)
  · exact (link3_203 w).symm.trans (hw 2 67)
  · exact (link3_204 w).symm.trans (hw 3 0)
  · exact (link3_205 w).symm.trans (hw 3 1)
  · exact (link3_206 w).symm.trans (hw 3 2)
  · exact (link3_207 w).symm.trans (hw 3 3)
  · exact (link3_208 w).symm.trans (hw 3 4)
  · exact (link3_209 w).symm.trans (hw 3 5)
  · exact (link3_210 w).symm.trans (hw 3 6)
  · exact (link3_211 w).symm.trans (hw 3 7)
  · exact (link3_212 w).symm.trans (hw 3 8)
  · exact (link3_213 w).symm.trans (hw 3 9)
  · exact (link3_214 w).symm.trans (hw 3 10)
  · exact (link3_215 w).symm.trans (hw 3 11)
  · exact (link3_216 w).symm.trans (hw 3 12)
  · exact (link3_217 w).symm.trans (hw 3 13)
  · exact (link3_218 w).symm.trans (hw 3 14)
  · exact (link3_219 w).symm.trans (hw 3 15)
  · exact (link3_220 w).symm.trans (hw 3 16)
  · exact (link3_221 w).symm.trans (hw 3 17)
  · exact (link3_222 w).symm.trans (hw 3 18)
  · exact (link3_223 w).symm.trans (hw 3 19)
  · exact (link3_224 w).symm.trans (hw 3 20)
  · exact (link3_225 w).symm.trans (hw 3 21)
  · exact (link3_226 w).symm.trans (hw 3 22)
  · exact (link3_227 w).symm.trans (hw 3 23)
  · exact (link3_228 w).symm.trans (hw 3 24)
  · exact (link3_229 w).symm.trans (hw 3 25)
  · exact (link3_230 w).symm.trans (hw 3 26)
  · exact (link3_231 w).symm.trans (hw 3 27)
  · exact (link3_232 w).symm.trans (hw 3 28)
  · exact (link3_233 w).symm.trans (hw 3 29)
  · exact (link3_234 w).symm.trans (hw 3 30)
  · exact (link3_235 w).symm.trans (hw 3 31)
  · exact (link3_236 w).symm.trans (hw 3 32)
  · exact (link3_237 w).symm.trans (hw 3 33)
  · exact (link3_238 w).symm.trans (hw 3 34)
  · exact (link3_239 w).symm.trans (hw 3 35)
  · exact (link3_240 w).symm.trans (hw 3 36)
  · exact (link3_241 w).symm.trans (hw 3 37)
  · exact (link3_242 w).symm.trans (hw 3 38)
  · exact (link3_243 w).symm.trans (hw 3 39)
  · exact (link3_244 w).symm.trans (hw 3 40)
  · exact (link3_245 w).symm.trans (hw 3 41)
  · exact (link3_246 w).symm.trans (hw 3 42)
  · exact (link3_247 w).symm.trans (hw 3 43)
  · exact (link3_248 w).symm.trans (hw 3 44)
  · exact (link3_249 w).symm.trans (hw 3 45)
  · exact (link3_250 w).symm.trans (hw 3 46)
  · exact (link3_251 w).symm.trans (hw 3 47)
  · exact (link3_252 w).symm.trans (hw 3 48)
  · exact (link3_253 w).symm.trans (hw 3 49)
  · exact (link3_254 w).symm.trans (hw 3 50)
  · exact (link3_255 w).symm.trans (hw 3 51)
  · exact (link3_256 w).symm.trans (hw 3 52)
  · exact (link3_257 w).symm.trans (hw 3 53)
  · exact (link3_258 w).symm.trans (hw 3 54)
  · exact (link3_259 w).symm.trans (hw 3 55)
  · exact (link3_260 w).symm.trans (hw 3 56)
  · exact (link3_261 w).symm.trans (hw 3 57)
  · exact (link3_262 w).symm.trans (hw 3 58)
  · exact (link3_263 w).symm.trans (hw 3 59)
  · exact (link3_264 w).symm.trans (hw 3 60)
  · exact (link3_265 w).symm.trans (hw 3 61)
  · exact (link3_266 w).symm.trans (hw 3 62)
  · exact (link3_267 w).symm.trans (hw 3 63)
  · exact (link3_268 w).symm.trans (hw 3 64)
  · exact (link3_269 w).symm.trans (hw 3 65)
  · exact (link3_270 w).symm.trans (hw 3 66)
  · exact (link3_271 w).symm.trans (hw 3 67)

#print axioms kernel_case3

end SmallLevelTwentyTwoJetBlock
end
end
