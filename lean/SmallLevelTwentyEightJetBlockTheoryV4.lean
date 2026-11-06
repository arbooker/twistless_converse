module

public import SmallLevelTwentyEightLaurentTheoryV4
public import SmallLevelTwentyEightThirdJetData0V1
public import SmallLevelTwentyOneThirdShiftScaleV1

/-! Consolidated chapter: SmallLevelTwentyEightJetBlock. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyEightJetBlockRowsV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightJetBlock
open Complex SmallLevelFiniteShift SmallLevelTwentyEightLaurent

def jetSlice (w : Fin 336→ℂ) (n : Fin 4) (j : Fin 84) : ℂ := w (finProdFinEquiv (n,j))

def jetBlockRow (n : Fin 4) (i : Fin 86) (w : Fin 336→ℂ) : ℂ :=
  leadingRows (-1) (-1) (2/2^n.val) (3/3^n.val) (7/7^n.val) (-10/3) (jetSlice w n) i-
    ∑ a∈Finset.range n.val, (1/((a+1).factorial:ℂ))*
      positiveTaylorRows (-1) (-1) (2/2^n.val) (3/3^n.val) (7/7^n.val) a
        (jetSlice w (lowerIndex n a)) i

end SmallLevelTwentyEightJetBlock
end
end

/-! ## SmallLevelTwentyEightJetBlockLinksCase0BundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightJetBlock
open Complex SmallLevelFiniteShift SmallLevelTwentyEightLaurent SmallLevelTwentyEightThirdJet

theorem link0_0 (w : Fin 336→ℂ) : jetBlockRow 0 0 w=rows0 w 0 := by
  change jetBlockRow 0 0 w=(1)*w 0 + ((-63))*w 82
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_0

theorem link0_1 (w : Fin 336→ℂ) : jetBlockRow 0 1 w=rows0 w 1 := by
  change jetBlockRow 0 1 w=(1)*w 0 + (28)*w 81
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_1

theorem link0_2 (w : Fin 336→ℂ) : jetBlockRow 0 2 w=rows0 w 2 := by
  change jetBlockRow 0 2 w=(1)*w 42 + (63)*w 82
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_2

theorem link0_3 (w : Fin 336→ℂ) : jetBlockRow 0 3 w=rows0 w 3 := by
  change jetBlockRow 0 3 w=(1)*w 0 + ((-7))*w 78
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_3

theorem link0_4 (w : Fin 336→ℂ) : jetBlockRow 0 4 w=rows0 w 4 := by
  change jetBlockRow 0 4 w=(1)*w 21 + ((-63)/4)*w 80
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_4

theorem link0_5 (w : Fin 336→ℂ) : jetBlockRow 0 5 w=rows0 w 5 := by
  change jetBlockRow 0 5 w=(1)*w 0
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_5

theorem link0_6 (w : Fin 336→ℂ) : jetBlockRow 0 6 w=rows0 w 6 := by
  change jetBlockRow 0 6 w=(1/252)*w 0 + (1)*w 1
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_6

theorem link0_7 (w : Fin 336→ℂ) : jetBlockRow 0 7 w=rows0 w 7 := by
  change jetBlockRow 0 7 w=(1)*w 2 + (1/63)*w 42
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_7

theorem link0_8 (w : Fin 336→ℂ) : jetBlockRow 0 8 w=rows0 w 8 := by
  change jetBlockRow 0 8 w=(1/28)*w 0 + (1)*w 3
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_8

theorem link0_9 (w : Fin 336→ℂ) : jetBlockRow 0 9 w=rows0 w 9 := by
  change jetBlockRow 0 9 w=(1)*w 4 + (4/63)*w 21
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_9

theorem link0_10 (w : Fin 336→ℂ) : jetBlockRow 0 10 w=rows0 w 10 := by
  change jetBlockRow 0 10 w=(1)*w 6 + (1/7)*w 42
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_10

theorem link0_11 (w : Fin 336→ℂ) : jetBlockRow 0 11 w=rows0 w 11 := by
  change jetBlockRow 0 11 w=(1)*w 7 + (7/36)*w 48
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_11

theorem link0_12 (w : Fin 336→ℂ) : jetBlockRow 0 12 w=rows0 w 12 := by
  change jetBlockRow 0 12 w=(1)*w 9 + (9/28)*w 56
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_12

theorem link0_13 (w : Fin 336→ℂ) : jetBlockRow 0 13 w=rows0 w 13 := by
  change jetBlockRow 0 13 w=(1)*w 12 + (4/7)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_13

theorem link0_14 (w : Fin 336→ℂ) : jetBlockRow 0 14 w=rows0 w 14 := by
  change jetBlockRow 0 14 w=(1)*w 14 + (7/9)*w 66
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_14

theorem link0_15 (w : Fin 336→ℂ) : jetBlockRow 0 15 w=rows0 w 15 := by
  change jetBlockRow 0 15 w=(1)*w 18 + (9/7)*w 70
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_15

theorem link0_16 (w : Fin 336→ℂ) : jetBlockRow 0 16 w=rows0 w 16 := by
  change jetBlockRow 0 16 w=(1)*w 21 + (7/4)*w 72
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_16

theorem link0_17 (w : Fin 336→ℂ) : jetBlockRow 0 17 w=rows0 w 17 := by
  change jetBlockRow 0 17 w=(1)*w 28 + (28/9)*w 75
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_17

theorem link0_18 (w : Fin 336→ℂ) : jetBlockRow 0 18 w=rows0 w 18 := by
  change jetBlockRow 0 18 w=(1)*w 36 + (36/7)*w 77
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_18

theorem link0_19 (w : Fin 336→ℂ) : jetBlockRow 0 19 w=rows0 w 19 := by
  change jetBlockRow 0 19 w=(1)*w 63 + (63/4)*w 80
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_19

theorem link0_20 (w : Fin 336→ℂ) : jetBlockRow 0 20 w=rows0 w 20 := by
  change jetBlockRow 0 20 w=(1)*w 6 + ((-36)/7)*w 7
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_20

theorem link0_21 (w : Fin 336→ℂ) : jetBlockRow 0 21 w=rows0 w 21 := by
  change jetBlockRow 0 21 w=((-28)/9)*w 9 + (1)*w 14
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_21

theorem link0_22 (w : Fin 336→ℂ) : jetBlockRow 0 22 w=rows0 w 22 := by
  change jetBlockRow 0 22 w=((-9)/7)*w 14 + (1)*w 24
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_22

theorem link0_23 (w : Fin 336→ℂ) : jetBlockRow 0 23 w=rows0 w 23 := by
  change jetBlockRow 0 23 w=((-7)/9)*w 18 + (1)*w 28
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_23

theorem link0_24 (w : Fin 336→ℂ) : jetBlockRow 0 24 w=rows0 w 24 := by
  change jetBlockRow 0 24 w=((-4)/7)*w 21 + (1)*w 30
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_24

theorem link0_25 (w : Fin 336→ℂ) : jetBlockRow 0 25 w=rows0 w 25 := by
  change jetBlockRow 0 25 w=((-9)/28)*w 28 + (1)*w 33
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_25

theorem link0_26 (w : Fin 336→ℂ) : jetBlockRow 0 26 w=rows0 w 26 := by
  change jetBlockRow 0 26 w=(1)*w 35 + ((-7)/36)*w 36
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_26

theorem link0_27 (w : Fin 336→ℂ) : jetBlockRow 0 27 w=rows0 w 27 := by
  change jetBlockRow 0 27 w=(1)*w 36 + ((-1)/7)*w 42
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_27

theorem link0_28 (w : Fin 336→ℂ) : jetBlockRow 0 28 w=rows0 w 28 := by
  change jetBlockRow 0 28 w=(1)*w 38 + ((-4)/63)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_28

theorem link0_29 (w : Fin 336→ℂ) : jetBlockRow 0 29 w=rows0 w 29 := by
  change jetBlockRow 0 29 w=((-1)/28)*w 0 + (1)*w 39
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_29

theorem link0_30 (w : Fin 336→ℂ) : jetBlockRow 0 30 w=rows0 w 30 := by
  change jetBlockRow 0 30 w=(1)*w 40 + ((-1)/63)*w 42
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_30

theorem link0_31 (w : Fin 336→ℂ) : jetBlockRow 0 31 w=rows0 w 31 := by
  change jetBlockRow 0 31 w=((-1)/252)*w 0 + (1)*w 41
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_31

theorem link0_32 (w : Fin 336→ℂ) : jetBlockRow 0 32 w=rows0 w 32 := by
  change jetBlockRow 0 32 w=((-1)/252)*w 0 + (1)*w 43
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_32

theorem link0_33 (w : Fin 336→ℂ) : jetBlockRow 0 33 w=rows0 w 33 := by
  change jetBlockRow 0 33 w=((-1)/63)*w 42 + (1)*w 44
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_33

theorem link0_34 (w : Fin 336→ℂ) : jetBlockRow 0 34 w=rows0 w 34 := by
  change jetBlockRow 0 34 w=((-1)/28)*w 0 + (1)*w 45
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_34

theorem link0_35 (w : Fin 336→ℂ) : jetBlockRow 0 35 w=rows0 w 35 := by
  change jetBlockRow 0 35 w=((-4)/63)*w 21 + (1)*w 46
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_35

theorem link0_36 (w : Fin 336→ℂ) : jetBlockRow 0 36 w=rows0 w 36 := by
  change jetBlockRow 0 36 w=((-7)/36)*w 48 + (1)*w 49
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_36

theorem link0_37 (w : Fin 336→ℂ) : jetBlockRow 0 37 w=rows0 w 37 := by
  change jetBlockRow 0 37 w=(1)*w 51 + ((-9)/28)*w 56
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_37

theorem link0_38 (w : Fin 336→ℂ) : jetBlockRow 0 38 w=rows0 w 38 := by
  change jetBlockRow 0 38 w=(1)*w 54 + ((-4)/7)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_38

theorem link0_39 (w : Fin 336→ℂ) : jetBlockRow 0 39 w=rows0 w 39 := by
  change jetBlockRow 0 39 w=(1)*w 60 + ((-9)/7)*w 70
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_39

theorem link0_40 (w : Fin 336→ℂ) : jetBlockRow 0 40 w=rows0 w 40 := by
  change jetBlockRow 0 40 w=(1/252)*w 0 + (1)*w 83
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_40

theorem link0_41 (w : Fin 336→ℂ) : jetBlockRow 0 41 w=rows0 w 41 := by
  change jetBlockRow 0 41 w=(1)*w 54 + (36)*w 79
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_41

theorem link0_42 (w : Fin 336→ℂ) : jetBlockRow 0 42 w=rows0 w 42 := by
  change jetBlockRow 0 42 w=(9)*w 8 + (1)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_42

theorem link0_43 (w : Fin 336→ℂ) : jetBlockRow 0 43 w=rows0 w 43 := by
  change jetBlockRow 0 43 w=(9/4)*w 10 + (1)*w 69
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_43

theorem link0_44 (w : Fin 336→ℂ) : jetBlockRow 0 44 w=rows0 w 44 := by
  change jetBlockRow 0 44 w=(4/9)*w 15 + (1)*w 74
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_44

theorem link0_45 (w : Fin 336→ℂ) : jetBlockRow 0 45 w=rows0 w 45 := by
  change jetBlockRow 0 45 w=(1/9)*w 24 + (1)*w 76
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_45

theorem link0_46 (w : Fin 336→ℂ) : jetBlockRow 0 46 w=rows0 w 46 := by
  change jetBlockRow 0 46 w=(1)*w 5 + (1/36)*w 30
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_46

theorem link0_47 (w : Fin 336→ℂ) : jetBlockRow 0 47 w=rows0 w 47 := by
  change jetBlockRow 0 47 w=(1)*w 5 + (1)*w 47
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_47

theorem link0_48 (w : Fin 336→ℂ) : jetBlockRow 0 48 w=rows0 w 48 := by
  change jetBlockRow 0 48 w=(1)*w 8 + (1)*w 50
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_48

theorem link0_49 (w : Fin 336→ℂ) : jetBlockRow 0 49 w=rows0 w 49 := by
  change jetBlockRow 0 49 w=(1)*w 10 + (1)*w 52
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_49

theorem link0_50 (w : Fin 336→ℂ) : jetBlockRow 0 50 w=rows0 w 50 := by
  change jetBlockRow 0 50 w=(1)*w 11 + (1)*w 53
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_50

theorem link0_51 (w : Fin 336→ℂ) : jetBlockRow 0 51 w=rows0 w 51 := by
  change jetBlockRow 0 51 w=(1)*w 13 + (1)*w 55
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_51

theorem link0_52 (w : Fin 336→ℂ) : jetBlockRow 0 52 w=rows0 w 52 := by
  change jetBlockRow 0 52 w=(1)*w 15 + (1)*w 57
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_52

theorem link0_53 (w : Fin 336→ℂ) : jetBlockRow 0 53 w=rows0 w 53 := by
  change jetBlockRow 0 53 w=(1)*w 16 + (1)*w 58
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_53

theorem link0_54 (w : Fin 336→ℂ) : jetBlockRow 0 54 w=rows0 w 54 := by
  change jetBlockRow 0 54 w=(1)*w 17 + (1)*w 59
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_54

theorem link0_55 (w : Fin 336→ℂ) : jetBlockRow 0 55 w=rows0 w 55 := by
  change jetBlockRow 0 55 w=(1)*w 19 + (1)*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_55

theorem link0_56 (w : Fin 336→ℂ) : jetBlockRow 0 56 w=rows0 w 56 := by
  change jetBlockRow 0 56 w=(1)*w 20 + (1)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_56

theorem link0_57 (w : Fin 336→ℂ) : jetBlockRow 0 57 w=rows0 w 57 := by
  change jetBlockRow 0 57 w=(1)*w 22 + (1)*w 64
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_57

theorem link0_58 (w : Fin 336→ℂ) : jetBlockRow 0 58 w=rows0 w 58 := by
  change jetBlockRow 0 58 w=(1)*w 23 + (1)*w 65
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_58

theorem link0_59 (w : Fin 336→ℂ) : jetBlockRow 0 59 w=rows0 w 59 := by
  change jetBlockRow 0 59 w=(1)*w 25 + (1)*w 67
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_59

theorem link0_60 (w : Fin 336→ℂ) : jetBlockRow 0 60 w=rows0 w 60 := by
  change jetBlockRow 0 60 w=(1)*w 26 + (1)*w 68
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_60

theorem link0_61 (w : Fin 336→ℂ) : jetBlockRow 0 61 w=rows0 w 61 := by
  change jetBlockRow 0 61 w=(1)*w 27 + (1)*w 69
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_61

theorem link0_62 (w : Fin 336→ℂ) : jetBlockRow 0 62 w=rows0 w 62 := by
  change jetBlockRow 0 62 w=(1)*w 29 + (1)*w 71
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_62

theorem link0_63 (w : Fin 336→ℂ) : jetBlockRow 0 63 w=rows0 w 63 := by
  change jetBlockRow 0 63 w=(1)*w 31 + (1)*w 73
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_63

theorem link0_64 (w : Fin 336→ℂ) : jetBlockRow 0 64 w=rows0 w 64 := by
  change jetBlockRow 0 64 w=(1)*w 32 + (1)*w 74
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_64

theorem link0_65 (w : Fin 336→ℂ) : jetBlockRow 0 65 w=rows0 w 65 := by
  change jetBlockRow 0 65 w=(1)*w 34 + (1)*w 76
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_65

theorem link0_66 (w : Fin 336→ℂ) : jetBlockRow 0 66 w=rows0 w 66 := by
  change jetBlockRow 0 66 w=(1)*w 37 + (1)*w 79
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_66

theorem link0_67 (w : Fin 336→ℂ) : jetBlockRow 0 67 w=rows0 w 67 := by
  change jetBlockRow 0 67 w=(1)*w 28 + (1)*w 56
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_67

theorem link0_68 (w : Fin 336→ℂ) : jetBlockRow 0 68 w=rows0 w 68 := by
  change jetBlockRow 0 68 w=(1/28)*w 0 + (1/28)*w 28 + (1)*w 29 + (1)*w 57
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_68

theorem link0_69 (w : Fin 336→ℂ) : jetBlockRow 0 69 w=rows0 w 69 := by
  change jetBlockRow 0 69 w=(1/28)*w 0 + (1)*w 27 + (1)*w 55 + (1/28)*w 56
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_69

theorem link0_70 (w : Fin 336→ℂ) : jetBlockRow 0 70 w=rows0 w 70 := by
  change jetBlockRow 0 70 w=(1/7)*w 14 + (1)*w 30 + (1/7)*w 42 + (1)*w 58
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_70

theorem link0_71 (w : Fin 336→ℂ) : jetBlockRow 0 71 w=rows0 w 71 := by
  change jetBlockRow 0 71 w=(1)*w 26 + (1/7)*w 42 + (1)*w 54 + (1/7)*w 70
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_71

theorem link0_72 (w : Fin 336→ℂ) : jetBlockRow 0 72 w=rows0 w 72 := by
  change jetBlockRow 0 72 w=(4/7)*w 21 + (1)*w 32 + (4/7)*w 49 + (1)*w 60
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_72

theorem link0_73 (w : Fin 336→ℂ) : jetBlockRow 0 73 w=rows0 w 73 := by
  change jetBlockRow 0 73 w=(1)*w 24 + (4/7)*w 35 + (1)*w 52 + (4/7)*w 63
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_73

theorem link0_74 (w : Fin 336→ℂ) : jetBlockRow 0 74 w=rows0 w 74 := by
  change jetBlockRow 0 74 w=(1/36)*w 0 + (1/36)*w 12 + (1)*w 13 + (1/36)*w 24 + (1)*w 25 + (1/36)*w 36 + (1)*w 37 + (1)*w 49 + (1/36)*w 60 + (1)*w 61 + (1/36)*w 72 + (1)*w 73
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_74

theorem link0_75 (w : Fin 336→ℂ) : jetBlockRow 0 75 w=rows0 w 75 := by
  change jetBlockRow 0 75 w=(1/36)*w 0 + (1)*w 11 + (1/36)*w 12 + (1)*w 23 + (1/36)*w 24 + (1)*w 35 + (1)*w 47 + (1/36)*w 48 + (1)*w 59 + (1/36)*w 60 + (1)*w 71 + (1/36)*w 72
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_75

theorem link0_76 (w : Fin 336→ℂ) : jetBlockRow 0 76 w=rows0 w 76 := by
  change jetBlockRow 0 76 w=(1/9)*w 6 + (1)*w 14 + (1/9)*w 18 + (1)*w 26 + (1/9)*w 30 + (1)*w 38 + (1/9)*w 42 + (1)*w 50 + (1/9)*w 54 + (1)*w 62 + (1)*w 74 + (1/9)*w 78
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_76

theorem link0_77 (w : Fin 336→ℂ) : jetBlockRow 0 77 w=rows0 w 77 := by
  change jetBlockRow 0 77 w=(1)*w 4 + (1)*w 8 + (1)*w 16 + (1)*w 20 + (1)*w 32 + (1)*w 40 + (1)*w 44 + (1)*w 52 + (1)*w 64 + (1)*w 68 + (1)*w 76 + (1)*w 80
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_77

theorem link0_78 (w : Fin 336→ℂ) : jetBlockRow 0 78 w=rows0 w 78 := by
  change jetBlockRow 0 78 w=(1)*w 3 + (10/9)*w 9 + (1/9)*w 27 + (1)*w 31 + (1)*w 59
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_78

theorem link0_79 (w : Fin 336→ℂ) : jetBlockRow 0 79 w=rows0 w 79 := by
  change jetBlockRow 0 79 w=(1)*w 5 + (10/9)*w 15 + (1)*w 33 + (1/9)*w 45 + (1)*w 61
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_79

theorem link0_80 (w : Fin 336→ℂ) : jetBlockRow 0 80 w=rows0 w 80 := by
  change jetBlockRow 0 80 w=(1)*w 6 + (10/9)*w 18 + (1)*w 34 + (1/9)*w 54 + (1)*w 62
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_80

theorem link0_81 (w : Fin 336→ℂ) : jetBlockRow 0 81 w=rows0 w 81 := by
  change jetBlockRow 0 81 w=(1)*w 9 + (10/9)*w 27 + (1)*w 37 + (1)*w 65 + (1/9)*w 81
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_81

theorem link0_82 (w : Fin 336→ℂ) : jetBlockRow 0 82 w=rows0 w 82 := by
  change jetBlockRow 0 82 w=(1)*w 53
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_82

theorem link0_83 (w : Fin 336→ℂ) : jetBlockRow 0 83 w=rows0 w 83 := by
  change jetBlockRow 0 83 w=(1/4)*w 0 + (1/4)*w 12 + (1)*w 15 + (1/4)*w 24 + (1)*w 27 + (1/4)*w 36 + (1)*w 39 + (1/4)*w 48 + (1)*w 51 + (1/4)*w 60 + (1)*w 63 + (1)*w 75
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_83

theorem link0_84 (w : Fin 336→ℂ) : jetBlockRow 0 84 w=rows0 w 84 := by
  change jetBlockRow 0 84 w=(1)*w 12 + (1)*w 24 + (1)*w 36 + (1)*w 48 + (1)*w 60 + (1)*w 72
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_84

theorem link0_85 (w : Fin 336→ℂ) : jetBlockRow 0 85 w=rows0 w 85 := by
  change jetBlockRow 0 85 w=(1)*w 8 + (10/9)*w 24 + (1)*w 36 + (1)*w 64 + (1/9)*w 72
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_85

theorem link0_86 (w : Fin 336→ℂ) : jetBlockRow 1 0 w=rows0 w 86 := by
  change jetBlockRow 1 0 w=((-42))*w 82 + (1)*w 84 + ((-1))*w 166
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_86

theorem link0_87 (w : Fin 336→ℂ) : jetBlockRow 1 1 w=rows0 w 87 := by
  change jetBlockRow 1 1 w=(28)*w 81 + (1)*w 84 + (1)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_87

theorem link0_88 (w : Fin 336→ℂ) : jetBlockRow 1 2 w=rows0 w 88 := by
  change jetBlockRow 1 2 w=(42)*w 82 + (1)*w 126 + (1)*w 166
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_88

theorem link0_89 (w : Fin 336→ℂ) : jetBlockRow 1 3 w=rows0 w 89 := by
  change jetBlockRow 1 3 w=((-14))*w 78 + (1)*w 84 + ((-1))*w 162
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_89

theorem link0_90 (w : Fin 336→ℂ) : jetBlockRow 1 4 w=rows0 w 90 := by
  change jetBlockRow 1 4 w=((-21))*w 80 + (1)*w 105 + ((-1))*w 164
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_90

theorem link0_91 (w : Fin 336→ℂ) : jetBlockRow 1 5 w=rows0 w 91 := by
  change jetBlockRow 1 5 w=(1)*w 84
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_91

theorem link0_92 (w : Fin 336→ℂ) : jetBlockRow 1 6 w=rows0 w 92 := by
  change jetBlockRow 1 6 w=(1/3)*w 0 + (1)*w 84 + (1)*w 85
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_92

theorem link0_93 (w : Fin 336→ℂ) : jetBlockRow 1 7 w=rows0 w 93 := by
  change jetBlockRow 1 7 w=(2/3)*w 42 + (1)*w 86 + (1)*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_93

theorem link0_94 (w : Fin 336→ℂ) : jetBlockRow 1 8 w=rows0 w 94 := by
  change jetBlockRow 1 8 w=(1)*w 0 + (1)*w 84 + (1)*w 87
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_94

theorem link0_95 (w : Fin 336→ℂ) : jetBlockRow 1 9 w=rows0 w 95 := by
  change jetBlockRow 1 9 w=(4/3)*w 21 + (1)*w 88 + (1)*w 105
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_95

theorem link0_96 (w : Fin 336→ℂ) : jetBlockRow 1 10 w=rows0 w 96 := by
  change jetBlockRow 1 10 w=(2)*w 42 + (1)*w 90 + (1)*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_96

theorem link0_97 (w : Fin 336→ℂ) : jetBlockRow 1 11 w=rows0 w 97 := by
  change jetBlockRow 1 11 w=(7/3)*w 48 + (1)*w 91 + (1)*w 132
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_97

theorem link0_98 (w : Fin 336→ℂ) : jetBlockRow 1 12 w=rows0 w 98 := by
  change jetBlockRow 1 12 w=(3)*w 56 + (1)*w 93 + (1)*w 140
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_98

theorem link0_99 (w : Fin 336→ℂ) : jetBlockRow 1 13 w=rows0 w 99 := by
  change jetBlockRow 1 13 w=(4)*w 63 + (1)*w 96 + (1)*w 147
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_99

theorem link0_100 (w : Fin 336→ℂ) : jetBlockRow 1 14 w=rows0 w 100 := by
  change jetBlockRow 1 14 w=(14/3)*w 66 + (1)*w 98 + (1)*w 150
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_100

theorem link0_101 (w : Fin 336→ℂ) : jetBlockRow 1 15 w=rows0 w 101 := by
  change jetBlockRow 1 15 w=(6)*w 70 + (1)*w 102 + (1)*w 154
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_101

theorem link0_102 (w : Fin 336→ℂ) : jetBlockRow 1 16 w=rows0 w 102 := by
  change jetBlockRow 1 16 w=(7)*w 72 + (1)*w 105 + (1)*w 156
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_102

theorem link0_103 (w : Fin 336→ℂ) : jetBlockRow 1 17 w=rows0 w 103 := by
  change jetBlockRow 1 17 w=(28/3)*w 75 + (1)*w 112 + (1)*w 159
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_103

theorem link0_104 (w : Fin 336→ℂ) : jetBlockRow 1 18 w=rows0 w 104 := by
  change jetBlockRow 1 18 w=(12)*w 77 + (1)*w 120 + (1)*w 161
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_104

theorem link0_105 (w : Fin 336→ℂ) : jetBlockRow 1 19 w=rows0 w 105 := by
  change jetBlockRow 1 19 w=(21)*w 80 + (1)*w 147 + (1)*w 164
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_105

theorem link0_106 (w : Fin 336→ℂ) : jetBlockRow 1 20 w=rows0 w 106 := by
  change jetBlockRow 1 20 w=(12)*w 7 + (1)*w 90 + ((-1))*w 91
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_106

theorem link0_107 (w : Fin 336→ℂ) : jetBlockRow 1 21 w=rows0 w 107 := by
  change jetBlockRow 1 21 w=(28/3)*w 9 + ((-1))*w 93 + (1)*w 98
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_107

theorem link0_108 (w : Fin 336→ℂ) : jetBlockRow 1 22 w=rows0 w 108 := by
  change jetBlockRow 1 22 w=(6)*w 14 + ((-1))*w 98 + (1)*w 108
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_108

theorem link0_109 (w : Fin 336→ℂ) : jetBlockRow 1 23 w=rows0 w 109 := by
  change jetBlockRow 1 23 w=(14/3)*w 18 + ((-1))*w 102 + (1)*w 112
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_109

theorem link0_110 (w : Fin 336→ℂ) : jetBlockRow 1 24 w=rows0 w 110 := by
  change jetBlockRow 1 24 w=(4)*w 21 + ((-1))*w 105 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_110

theorem link0_111 (w : Fin 336→ℂ) : jetBlockRow 1 25 w=rows0 w 111 := by
  change jetBlockRow 1 25 w=(3)*w 28 + ((-1))*w 112 + (1)*w 117
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_111

theorem link0_112 (w : Fin 336→ℂ) : jetBlockRow 1 26 w=rows0 w 112 := by
  change jetBlockRow 1 26 w=(7/3)*w 36 + (1)*w 119 + ((-1))*w 120
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_112

theorem link0_113 (w : Fin 336→ℂ) : jetBlockRow 1 27 w=rows0 w 113 := by
  change jetBlockRow 1 27 w=(2)*w 42 + (1)*w 120 + ((-1))*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_113

theorem link0_114 (w : Fin 336→ℂ) : jetBlockRow 1 28 w=rows0 w 114 := by
  change jetBlockRow 1 28 w=(4/3)*w 63 + (1)*w 122 + ((-1))*w 147
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_114

theorem link0_115 (w : Fin 336→ℂ) : jetBlockRow 1 29 w=rows0 w 115 := by
  change jetBlockRow 1 29 w=(1)*w 0 + ((-1))*w 84 + (1)*w 123
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_115

theorem link0_116 (w : Fin 336→ℂ) : jetBlockRow 1 30 w=rows0 w 116 := by
  change jetBlockRow 1 30 w=(2/3)*w 42 + (1)*w 124 + ((-1))*w 126
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_116

theorem link0_117 (w : Fin 336→ℂ) : jetBlockRow 1 31 w=rows0 w 117 := by
  change jetBlockRow 1 31 w=(1/3)*w 0 + ((-1))*w 84 + (1)*w 125
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_117

theorem link0_118 (w : Fin 336→ℂ) : jetBlockRow 1 32 w=rows0 w 118 := by
  change jetBlockRow 1 32 w=((-1)/3)*w 0 + ((-1))*w 84 + (1)*w 127
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_118

theorem link0_119 (w : Fin 336→ℂ) : jetBlockRow 1 33 w=rows0 w 119 := by
  change jetBlockRow 1 33 w=((-2)/3)*w 42 + ((-1))*w 126 + (1)*w 128
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_119

theorem link0_120 (w : Fin 336→ℂ) : jetBlockRow 1 34 w=rows0 w 120 := by
  change jetBlockRow 1 34 w=((-1))*w 0 + ((-1))*w 84 + (1)*w 129
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_120

theorem link0_121 (w : Fin 336→ℂ) : jetBlockRow 1 35 w=rows0 w 121 := by
  change jetBlockRow 1 35 w=((-4)/3)*w 21 + ((-1))*w 105 + (1)*w 130
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_121

theorem link0_122 (w : Fin 336→ℂ) : jetBlockRow 1 36 w=rows0 w 122 := by
  change jetBlockRow 1 36 w=((-7)/3)*w 48 + ((-1))*w 132 + (1)*w 133
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_122

theorem link0_123 (w : Fin 336→ℂ) : jetBlockRow 1 37 w=rows0 w 123 := by
  change jetBlockRow 1 37 w=((-3))*w 56 + (1)*w 135 + ((-1))*w 140
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_123

theorem link0_124 (w : Fin 336→ℂ) : jetBlockRow 1 38 w=rows0 w 124 := by
  change jetBlockRow 1 38 w=((-4))*w 63 + (1)*w 138 + ((-1))*w 147
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_124

theorem link0_125 (w : Fin 336→ℂ) : jetBlockRow 1 39 w=rows0 w 125 := by
  change jetBlockRow 1 39 w=((-6))*w 70 + (1)*w 144 + ((-1))*w 154
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_125

theorem link0_126 (w : Fin 336→ℂ) : jetBlockRow 1 40 w=rows0 w 126 := by
  change jetBlockRow 1 40 w=((-1)/3)*w 0 + (1)*w 84 + (1)*w 167
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_126

theorem link0_127 (w : Fin 336→ℂ) : jetBlockRow 1 41 w=rows0 w 127 := by
  change jetBlockRow 1 41 w=((-84))*w 79 + (1)*w 138 + (1)*w 163
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_127

theorem link0_128 (w : Fin 336→ℂ) : jetBlockRow 1 42 w=rows0 w 128 := by
  change jetBlockRow 1 42 w=((-42))*w 8 + (1)*w 92 + (1)*w 144
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_128

theorem link0_129 (w : Fin 336→ℂ) : jetBlockRow 1 43 w=rows0 w 129 := by
  change jetBlockRow 1 43 w=((-21))*w 10 + (1)*w 94 + (1)*w 153
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_129

theorem link0_130 (w : Fin 336→ℂ) : jetBlockRow 1 44 w=rows0 w 130 := by
  change jetBlockRow 1 44 w=((-28)/3)*w 15 + (1)*w 99 + (1)*w 158
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_130

theorem link0_131 (w : Fin 336→ℂ) : jetBlockRow 1 45 w=rows0 w 131 := by
  change jetBlockRow 1 45 w=((-14)/3)*w 24 + (1)*w 108 + (1)*w 160
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_131

theorem link0_132 (w : Fin 336→ℂ) : jetBlockRow 1 46 w=rows0 w 132 := by
  change jetBlockRow 1 46 w=((-7)/3)*w 30 + (1)*w 89 + (1)*w 114
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_132

theorem link0_133 (w : Fin 336→ℂ) : jetBlockRow 1 47 w=rows0 w 133 := by
  change jetBlockRow 1 47 w=(1)*w 89 + (1)*w 131
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_133

theorem link0_134 (w : Fin 336→ℂ) : jetBlockRow 1 48 w=rows0 w 134 := by
  change jetBlockRow 1 48 w=(1)*w 92 + (1)*w 134
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_134

theorem link0_135 (w : Fin 336→ℂ) : jetBlockRow 1 49 w=rows0 w 135 := by
  change jetBlockRow 1 49 w=(1)*w 94 + (1)*w 136
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_135

theorem link0_136 (w : Fin 336→ℂ) : jetBlockRow 1 50 w=rows0 w 136 := by
  change jetBlockRow 1 50 w=(1)*w 95 + (1)*w 137
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_136

theorem link0_137 (w : Fin 336→ℂ) : jetBlockRow 1 51 w=rows0 w 137 := by
  change jetBlockRow 1 51 w=(1)*w 97 + (1)*w 139
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_137

theorem link0_138 (w : Fin 336→ℂ) : jetBlockRow 1 52 w=rows0 w 138 := by
  change jetBlockRow 1 52 w=(1)*w 99 + (1)*w 141
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_138

theorem link0_139 (w : Fin 336→ℂ) : jetBlockRow 1 53 w=rows0 w 139 := by
  change jetBlockRow 1 53 w=(1)*w 100 + (1)*w 142
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_139

theorem link0_140 (w : Fin 336→ℂ) : jetBlockRow 1 54 w=rows0 w 140 := by
  change jetBlockRow 1 54 w=(1)*w 101 + (1)*w 143
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_140

theorem link0_141 (w : Fin 336→ℂ) : jetBlockRow 1 55 w=rows0 w 141 := by
  change jetBlockRow 1 55 w=(1)*w 103 + (1)*w 145
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_141

theorem link0_142 (w : Fin 336→ℂ) : jetBlockRow 1 56 w=rows0 w 142 := by
  change jetBlockRow 1 56 w=(1)*w 104 + (1)*w 146
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_142

theorem link0_143 (w : Fin 336→ℂ) : jetBlockRow 1 57 w=rows0 w 143 := by
  change jetBlockRow 1 57 w=(1)*w 106 + (1)*w 148
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_143

theorem link0_144 (w : Fin 336→ℂ) : jetBlockRow 1 58 w=rows0 w 144 := by
  change jetBlockRow 1 58 w=(1)*w 107 + (1)*w 149
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_144

theorem link0_145 (w : Fin 336→ℂ) : jetBlockRow 1 59 w=rows0 w 145 := by
  change jetBlockRow 1 59 w=(1)*w 109 + (1)*w 151
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_145

theorem link0_146 (w : Fin 336→ℂ) : jetBlockRow 1 60 w=rows0 w 146 := by
  change jetBlockRow 1 60 w=(1)*w 110 + (1)*w 152
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_146

theorem link0_147 (w : Fin 336→ℂ) : jetBlockRow 1 61 w=rows0 w 147 := by
  change jetBlockRow 1 61 w=(1)*w 111 + (1)*w 153
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_147

theorem link0_148 (w : Fin 336→ℂ) : jetBlockRow 1 62 w=rows0 w 148 := by
  change jetBlockRow 1 62 w=(1)*w 113 + (1)*w 155
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_148

theorem link0_149 (w : Fin 336→ℂ) : jetBlockRow 1 63 w=rows0 w 149 := by
  change jetBlockRow 1 63 w=(1)*w 115 + (1)*w 157
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_149

theorem link0_150 (w : Fin 336→ℂ) : jetBlockRow 1 64 w=rows0 w 150 := by
  change jetBlockRow 1 64 w=(1)*w 116 + (1)*w 158
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_150

theorem link0_151 (w : Fin 336→ℂ) : jetBlockRow 1 65 w=rows0 w 151 := by
  change jetBlockRow 1 65 w=(1)*w 118 + (1)*w 160
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_151

theorem link0_152 (w : Fin 336→ℂ) : jetBlockRow 1 66 w=rows0 w 152 := by
  change jetBlockRow 1 66 w=(1)*w 121 + (1)*w 163
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_152

theorem link0_153 (w : Fin 336→ℂ) : jetBlockRow 1 67 w=rows0 w 153 := by
  change jetBlockRow 1 67 w=(1)*w 112 + (1)*w 140
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_153

theorem link0_154 (w : Fin 336→ℂ) : jetBlockRow 1 68 w=rows0 w 154 := by
  change jetBlockRow 1 68 w=(3)*w 0 + (3)*w 28 + (1)*w 84 + (1)*w 112 + (1)*w 113 + (1)*w 141
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_154

theorem link0_155 (w : Fin 336→ℂ) : jetBlockRow 1 69 w=rows0 w 155 := by
  change jetBlockRow 1 69 w=((-3))*w 0 + ((-3))*w 56 + (1)*w 84 + (1)*w 111 + (1)*w 139 + (1)*w 140
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_155

theorem link0_156 (w : Fin 336→ℂ) : jetBlockRow 1 70 w=rows0 w 156 := by
  change jetBlockRow 1 70 w=(6)*w 14 + (6)*w 42 + (1)*w 98 + (1)*w 114 + (1)*w 126 + (1)*w 142
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_156

theorem link0_157 (w : Fin 336→ℂ) : jetBlockRow 1 71 w=rows0 w 157 := by
  change jetBlockRow 1 71 w=((-6))*w 42 + ((-6))*w 70 + (1)*w 110 + (1)*w 126 + (1)*w 138 + (1)*w 154
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_157

theorem link0_158 (w : Fin 336→ℂ) : jetBlockRow 1 72 w=rows0 w 158 := by
  change jetBlockRow 1 72 w=(12)*w 21 + (12)*w 49 + (1)*w 105 + (1)*w 116 + (1)*w 133 + (1)*w 144
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_158

theorem link0_159 (w : Fin 336→ℂ) : jetBlockRow 1 73 w=rows0 w 159 := by
  change jetBlockRow 1 73 w=((-12))*w 35 + ((-12))*w 63 + (1)*w 108 + (1)*w 119 + (1)*w 136 + (1)*w 147
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_159

theorem link0_160 (w : Fin 336→ℂ) : jetBlockRow 1 74 w=rows0 w 160 := by
  change jetBlockRow 1 74 w=(7/3)*w 0 + (7/3)*w 12 + (7/3)*w 24 + (7/3)*w 36 + (7/3)*w 60 + (7/3)*w 72 + (1)*w 84 + (1)*w 96 + (1)*w 97 + (1)*w 108 + (1)*w 109 + (1)*w 120 + (1)*w 121 + (1)*w 133 + (1)*w 144 + (1)*w 145 + (1)*w 156 + (1)*w 157
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_160

theorem link0_161 (w : Fin 336→ℂ) : jetBlockRow 1 75 w=rows0 w 161 := by
  change jetBlockRow 1 75 w=((-7)/3)*w 0 + ((-7)/3)*w 12 + ((-7)/3)*w 24 + ((-7)/3)*w 48 + ((-7)/3)*w 60 + ((-7)/3)*w 72 + (1)*w 84 + (1)*w 95 + (1)*w 96 + (1)*w 107 + (1)*w 108 + (1)*w 119 + (1)*w 131 + (1)*w 132 + (1)*w 143 + (1)*w 144 + (1)*w 155 + (1)*w 156
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_161

theorem link0_162 (w : Fin 336→ℂ) : jetBlockRow 1 76 w=rows0 w 162 := by
  change jetBlockRow 1 76 w=(14/3)*w 6 + (14/3)*w 18 + (14/3)*w 30 + (14/3)*w 42 + (14/3)*w 54 + (14/3)*w 78 + (1)*w 90 + (1)*w 98 + (1)*w 102 + (1)*w 110 + (1)*w 114 + (1)*w 122 + (1)*w 126 + (1)*w 134 + (1)*w 138 + (1)*w 146 + (1)*w 158 + (1)*w 162
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_162

theorem link0_163 (w : Fin 336→ℂ) : jetBlockRow 1 77 w=rows0 w 163 := by
  change jetBlockRow 1 77 w=(1)*w 88 + (1)*w 92 + (1)*w 100 + (1)*w 104 + (1)*w 116 + (1)*w 124 + (1)*w 128 + (1)*w 136 + (1)*w 148 + (1)*w 152 + (1)*w 160 + (1)*w 164
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_163

theorem link0_164 (w : Fin 336→ℂ) : jetBlockRow 1 78 w=rows0 w 164 := by
  change jetBlockRow 1 78 w=(1)*w 87 + (10/3)*w 93 + (1)*w 111 + (1)*w 115 + (1)*w 143
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_164

theorem link0_165 (w : Fin 336→ℂ) : jetBlockRow 1 79 w=rows0 w 165 := by
  change jetBlockRow 1 79 w=(1)*w 89 + (10/3)*w 99 + (1)*w 117 + (1)*w 129 + (1)*w 145
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_165

theorem link0_166 (w : Fin 336→ℂ) : jetBlockRow 1 80 w=rows0 w 166 := by
  change jetBlockRow 1 80 w=(1)*w 90 + (10/3)*w 102 + (1)*w 118 + (1)*w 138 + (1)*w 146
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_166

theorem link0_167 (w : Fin 336→ℂ) : jetBlockRow 1 81 w=rows0 w 167 := by
  change jetBlockRow 1 81 w=(1)*w 93 + (10/3)*w 111 + (1)*w 121 + (1)*w 149 + (1)*w 165
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_167

theorem link0_168 (w : Fin 336→ℂ) : jetBlockRow 1 82 w=rows0 w 168 := by
  change jetBlockRow 1 82 w=(1)*w 137
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_168

theorem link0_169 (w : Fin 336→ℂ) : jetBlockRow 1 83 w=rows0 w 169 := by
  change jetBlockRow 1 83 w=(7)*w 0 + (7)*w 12 + (7)*w 24 + (7)*w 36 + (7)*w 48 + (7)*w 60 + (1)*w 84 + (1)*w 96 + (1)*w 99 + (1)*w 108 + (1)*w 111 + (1)*w 120 + (1)*w 123 + (1)*w 132 + (1)*w 135 + (1)*w 144 + (1)*w 147 + (1)*w 159
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_169

theorem link0_170 (w : Fin 336→ℂ) : jetBlockRow 1 84 w=rows0 w 170 := by
  change jetBlockRow 1 84 w=(1)*w 96 + (1)*w 108 + (1)*w 120 + (1)*w 132 + (1)*w 144 + (1)*w 156
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_170

theorem link0_171 (w : Fin 336→ℂ) : jetBlockRow 1 85 w=rows0 w 171 := by
  change jetBlockRow 1 85 w=(1)*w 92 + (10/3)*w 108 + (1)*w 120 + (1)*w 148 + (1)*w 156
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_171

theorem link0_172 (w : Fin 336→ℂ) : jetBlockRow 2 0 w=rows0 w 172 := by
  change jetBlockRow 2 0 w=((-14))*w 82 + ((-2)/3)*w 166 + (1)*w 168 + ((-1)/63)*w 250
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_172

theorem link0_173 (w : Fin 336→ℂ) : jetBlockRow 2 1 w=rows0 w 173 := by
  change jetBlockRow 2 1 w=(14)*w 81 + (1)*w 165 + (1)*w 168 + (1/28)*w 249
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_173

theorem link0_174 (w : Fin 336→ℂ) : jetBlockRow 2 2 w=rows0 w 174 := by
  change jetBlockRow 2 2 w=(14)*w 82 + (2/3)*w 166 + (1)*w 210 + (1/63)*w 250
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_174

theorem link0_175 (w : Fin 336→ℂ) : jetBlockRow 2 3 w=rows0 w 175 := by
  change jetBlockRow 2 3 w=((-14))*w 78 + ((-2))*w 162 + (1)*w 168 + ((-1)/7)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_175

theorem link0_176 (w : Fin 336→ℂ) : jetBlockRow 2 4 w=rows0 w 176 := by
  change jetBlockRow 2 4 w=((-14))*w 80 + ((-4)/3)*w 164 + (1)*w 189 + ((-4)/63)*w 248
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_176

theorem link0_177 (w : Fin 336→ℂ) : jetBlockRow 2 5 w=rows0 w 177 := by
  change jetBlockRow 2 5 w=(1)*w 168
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_177

theorem link0_178 (w : Fin 336→ℂ) : jetBlockRow 2 6 w=rows0 w 178 := by
  change jetBlockRow 2 6 w=(14)*w 0 + (84)*w 84 + (252)*w 168 + (1)*w 169
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_178

theorem link0_179 (w : Fin 336→ℂ) : jetBlockRow 2 7 w=rows0 w 179 := by
  change jetBlockRow 2 7 w=(14)*w 42 + (42)*w 126 + (1)*w 170 + (63)*w 210
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_179

theorem link0_180 (w : Fin 336→ℂ) : jetBlockRow 2 8 w=rows0 w 180 := by
  change jetBlockRow 2 8 w=(14)*w 0 + (28)*w 84 + (28)*w 168 + (1)*w 171
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_180

theorem link0_181 (w : Fin 336→ℂ) : jetBlockRow 2 9 w=rows0 w 181 := by
  change jetBlockRow 2 9 w=(14)*w 21 + (21)*w 105 + (1)*w 172 + (63/4)*w 189
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_181

theorem link0_182 (w : Fin 336→ℂ) : jetBlockRow 2 10 w=rows0 w 182 := by
  change jetBlockRow 2 10 w=(14)*w 42 + (14)*w 126 + (1)*w 174 + (7)*w 210
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_182

theorem link0_183 (w : Fin 336→ℂ) : jetBlockRow 2 11 w=rows0 w 183 := by
  change jetBlockRow 2 11 w=(14)*w 48 + (12)*w 132 + (1)*w 175 + (36/7)*w 216
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_183

theorem link0_184 (w : Fin 336→ℂ) : jetBlockRow 2 12 w=rows0 w 184 := by
  change jetBlockRow 2 12 w=(14)*w 56 + (28/3)*w 140 + (1)*w 177 + (28/9)*w 224
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_184

theorem link0_185 (w : Fin 336→ℂ) : jetBlockRow 2 13 w=rows0 w 185 := by
  change jetBlockRow 2 13 w=(14)*w 63 + (7)*w 147 + (1)*w 180 + (7/4)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_185

theorem link0_186 (w : Fin 336→ℂ) : jetBlockRow 2 14 w=rows0 w 186 := by
  change jetBlockRow 2 14 w=(14)*w 66 + (6)*w 150 + (1)*w 182 + (9/7)*w 234
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_186

theorem link0_187 (w : Fin 336→ℂ) : jetBlockRow 2 15 w=rows0 w 187 := by
  change jetBlockRow 2 15 w=(14)*w 70 + (14/3)*w 154 + (1)*w 186 + (7/9)*w 238
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_187

theorem link0_188 (w : Fin 336→ℂ) : jetBlockRow 2 16 w=rows0 w 188 := by
  change jetBlockRow 2 16 w=(14)*w 72 + (4)*w 156 + (1)*w 189 + (4/7)*w 240
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_188

theorem link0_189 (w : Fin 336→ℂ) : jetBlockRow 2 17 w=rows0 w 189 := by
  change jetBlockRow 2 17 w=(14)*w 75 + (3)*w 159 + (1)*w 196 + (9/28)*w 243
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_189

theorem link0_190 (w : Fin 336→ℂ) : jetBlockRow 2 18 w=rows0 w 190 := by
  change jetBlockRow 2 18 w=(14)*w 77 + (7/3)*w 161 + (1)*w 204 + (7/36)*w 245
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_190

theorem link0_191 (w : Fin 336→ℂ) : jetBlockRow 2 19 w=rows0 w 191 := by
  change jetBlockRow 2 19 w=(14)*w 80 + (4/3)*w 164 + (1)*w 231 + (4/63)*w 248
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_191

theorem link0_192 (w : Fin 336→ℂ) : jetBlockRow 2 20 w=rows0 w 192 := by
  change jetBlockRow 2 20 w=((-14))*w 7 + (7/3)*w 91 + (1)*w 174 + ((-7)/36)*w 175
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_192

theorem link0_193 (w : Fin 336→ℂ) : jetBlockRow 2 21 w=rows0 w 193 := by
  change jetBlockRow 2 21 w=((-14))*w 9 + (3)*w 93 + ((-9)/28)*w 177 + (1)*w 182
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_193

theorem link0_194 (w : Fin 336→ℂ) : jetBlockRow 2 22 w=rows0 w 194 := by
  change jetBlockRow 2 22 w=((-14))*w 14 + (14/3)*w 98 + ((-7)/9)*w 182 + (1)*w 192
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_194

theorem link0_195 (w : Fin 336→ℂ) : jetBlockRow 2 23 w=rows0 w 195 := by
  change jetBlockRow 2 23 w=((-14))*w 18 + (6)*w 102 + ((-9)/7)*w 186 + (1)*w 196
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_195

theorem link0_196 (w : Fin 336→ℂ) : jetBlockRow 2 24 w=rows0 w 196 := by
  change jetBlockRow 2 24 w=((-14))*w 21 + (7)*w 105 + ((-7)/4)*w 189 + (1)*w 198
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_196

theorem link0_197 (w : Fin 336→ℂ) : jetBlockRow 2 25 w=rows0 w 197 := by
  change jetBlockRow 2 25 w=((-14))*w 28 + (28/3)*w 112 + ((-28)/9)*w 196 + (1)*w 201
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_197

theorem link0_198 (w : Fin 336→ℂ) : jetBlockRow 2 26 w=rows0 w 198 := by
  change jetBlockRow 2 26 w=((-14))*w 36 + (12)*w 120 + (1)*w 203 + ((-36)/7)*w 204
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_198

theorem link0_199 (w : Fin 336→ℂ) : jetBlockRow 2 27 w=rows0 w 199 := by
  change jetBlockRow 2 27 w=((-14))*w 42 + (14)*w 126 + (1)*w 204 + ((-7))*w 210
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_199

theorem link0_200 (w : Fin 336→ℂ) : jetBlockRow 2 28 w=rows0 w 200 := by
  change jetBlockRow 2 28 w=((-14))*w 63 + (21)*w 147 + (1)*w 206 + ((-63)/4)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_200

theorem link0_201 (w : Fin 336→ℂ) : jetBlockRow 2 29 w=rows0 w 201 := by
  change jetBlockRow 2 29 w=((-14))*w 0 + (28)*w 84 + ((-28))*w 168 + (1)*w 207
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_201

theorem link0_202 (w : Fin 336→ℂ) : jetBlockRow 2 30 w=rows0 w 202 := by
  change jetBlockRow 2 30 w=((-14))*w 42 + (42)*w 126 + (1)*w 208 + ((-63))*w 210
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_202

theorem link0_203 (w : Fin 336→ℂ) : jetBlockRow 2 31 w=rows0 w 203 := by
  change jetBlockRow 2 31 w=((-14))*w 0 + (84)*w 84 + ((-252))*w 168 + (1)*w 209
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_203

theorem link0_204 (w : Fin 336→ℂ) : jetBlockRow 2 32 w=rows0 w 204 := by
  change jetBlockRow 2 32 w=((-14))*w 0 + ((-84))*w 84 + ((-252))*w 168 + (1)*w 211
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_204

theorem link0_205 (w : Fin 336→ℂ) : jetBlockRow 2 33 w=rows0 w 205 := by
  change jetBlockRow 2 33 w=((-14))*w 42 + ((-42))*w 126 + ((-63))*w 210 + (1)*w 212
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_205

theorem link0_206 (w : Fin 336→ℂ) : jetBlockRow 2 34 w=rows0 w 206 := by
  change jetBlockRow 2 34 w=((-14))*w 0 + ((-28))*w 84 + ((-28))*w 168 + (1)*w 213
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_206

theorem link0_207 (w : Fin 336→ℂ) : jetBlockRow 2 35 w=rows0 w 207 := by
  change jetBlockRow 2 35 w=((-14))*w 21 + ((-21))*w 105 + ((-63)/4)*w 189 + (1)*w 214
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_207

theorem link0_208 (w : Fin 336→ℂ) : jetBlockRow 2 36 w=rows0 w 208 := by
  change jetBlockRow 2 36 w=((-14))*w 48 + ((-12))*w 132 + ((-36)/7)*w 216 + (1)*w 217
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_208

theorem link0_209 (w : Fin 336→ℂ) : jetBlockRow 2 37 w=rows0 w 209 := by
  change jetBlockRow 2 37 w=((-14))*w 56 + ((-28)/3)*w 140 + (1)*w 219 + ((-28)/9)*w 224
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_209

theorem link0_210 (w : Fin 336→ℂ) : jetBlockRow 2 38 w=rows0 w 210 := by
  change jetBlockRow 2 38 w=((-14))*w 63 + ((-7))*w 147 + (1)*w 222 + ((-7)/4)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_210

theorem link0_211 (w : Fin 336→ℂ) : jetBlockRow 2 39 w=rows0 w 211 := by
  change jetBlockRow 2 39 w=((-14))*w 70 + ((-14)/3)*w 154 + (1)*w 228 + ((-7)/9)*w 238
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_211

theorem link0_212 (w : Fin 336→ℂ) : jetBlockRow 2 40 w=rows0 w 212 := by
  change jetBlockRow 2 40 w=(14)*w 0 + ((-84))*w 84 + (252)*w 168 + (1)*w 251
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_212

theorem link0_213 (w : Fin 336→ℂ) : jetBlockRow 2 41 w=rows0 w 213 := by
  change jetBlockRow 2 41 w=(98)*w 79 + ((-7)/3)*w 163 + (1)*w 222 + (1/36)*w 247
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_213

theorem link0_214 (w : Fin 336→ℂ) : jetBlockRow 2 42 w=rows0 w 214 := by
  change jetBlockRow 2 42 w=(98)*w 8 + ((-14)/3)*w 92 + (1/9)*w 176 + (1)*w 228
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_214

theorem link0_215 (w : Fin 336→ℂ) : jetBlockRow 2 43 w=rows0 w 215 := by
  change jetBlockRow 2 43 w=(98)*w 10 + ((-28)/3)*w 94 + (4/9)*w 178 + (1)*w 237
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_215

theorem link0_216 (w : Fin 336→ℂ) : jetBlockRow 2 44 w=rows0 w 216 := by
  change jetBlockRow 2 44 w=(98)*w 15 + ((-21))*w 99 + (9/4)*w 183 + (1)*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_216

theorem link0_217 (w : Fin 336→ℂ) : jetBlockRow 2 45 w=rows0 w 217 := by
  change jetBlockRow 2 45 w=(98)*w 24 + ((-42))*w 108 + (9)*w 192 + (1)*w 244
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_217

theorem link0_218 (w : Fin 336→ℂ) : jetBlockRow 2 46 w=rows0 w 218 := by
  change jetBlockRow 2 46 w=(98)*w 30 + ((-84))*w 114 + (1)*w 173 + (36)*w 198
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_218

theorem link0_219 (w : Fin 336→ℂ) : jetBlockRow 2 47 w=rows0 w 219 := by
  change jetBlockRow 2 47 w=(1)*w 173 + (1)*w 215
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_219

theorem link0_220 (w : Fin 336→ℂ) : jetBlockRow 2 48 w=rows0 w 220 := by
  change jetBlockRow 2 48 w=(1)*w 176 + (1)*w 218
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_220

theorem link0_221 (w : Fin 336→ℂ) : jetBlockRow 2 49 w=rows0 w 221 := by
  change jetBlockRow 2 49 w=(1)*w 178 + (1)*w 220
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_221

theorem link0_222 (w : Fin 336→ℂ) : jetBlockRow 2 50 w=rows0 w 222 := by
  change jetBlockRow 2 50 w=(1)*w 179 + (1)*w 221
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_222

theorem link0_223 (w : Fin 336→ℂ) : jetBlockRow 2 51 w=rows0 w 223 := by
  change jetBlockRow 2 51 w=(1)*w 181 + (1)*w 223
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_223

theorem link0_224 (w : Fin 336→ℂ) : jetBlockRow 2 52 w=rows0 w 224 := by
  change jetBlockRow 2 52 w=(1)*w 183 + (1)*w 225
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_224

theorem link0_225 (w : Fin 336→ℂ) : jetBlockRow 2 53 w=rows0 w 225 := by
  change jetBlockRow 2 53 w=(1)*w 184 + (1)*w 226
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_225

theorem link0_226 (w : Fin 336→ℂ) : jetBlockRow 2 54 w=rows0 w 226 := by
  change jetBlockRow 2 54 w=(1)*w 185 + (1)*w 227
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_226

theorem link0_227 (w : Fin 336→ℂ) : jetBlockRow 2 55 w=rows0 w 227 := by
  change jetBlockRow 2 55 w=(1)*w 187 + (1)*w 229
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_227

theorem link0_228 (w : Fin 336→ℂ) : jetBlockRow 2 56 w=rows0 w 228 := by
  change jetBlockRow 2 56 w=(1)*w 188 + (1)*w 230
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_228

theorem link0_229 (w : Fin 336→ℂ) : jetBlockRow 2 57 w=rows0 w 229 := by
  change jetBlockRow 2 57 w=(1)*w 190 + (1)*w 232
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_229

theorem link0_230 (w : Fin 336→ℂ) : jetBlockRow 2 58 w=rows0 w 230 := by
  change jetBlockRow 2 58 w=(1)*w 191 + (1)*w 233
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_230

theorem link0_231 (w : Fin 336→ℂ) : jetBlockRow 2 59 w=rows0 w 231 := by
  change jetBlockRow 2 59 w=(1)*w 193 + (1)*w 235
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_231

theorem link0_232 (w : Fin 336→ℂ) : jetBlockRow 2 60 w=rows0 w 232 := by
  change jetBlockRow 2 60 w=(1)*w 194 + (1)*w 236
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_232

theorem link0_233 (w : Fin 336→ℂ) : jetBlockRow 2 61 w=rows0 w 233 := by
  change jetBlockRow 2 61 w=(1)*w 195 + (1)*w 237
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_233

theorem link0_234 (w : Fin 336→ℂ) : jetBlockRow 2 62 w=rows0 w 234 := by
  change jetBlockRow 2 62 w=(1)*w 197 + (1)*w 239
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_234

theorem link0_235 (w : Fin 336→ℂ) : jetBlockRow 2 63 w=rows0 w 235 := by
  change jetBlockRow 2 63 w=(1)*w 199 + (1)*w 241
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_235

theorem link0_236 (w : Fin 336→ℂ) : jetBlockRow 2 64 w=rows0 w 236 := by
  change jetBlockRow 2 64 w=(1)*w 200 + (1)*w 242
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_236

theorem link0_237 (w : Fin 336→ℂ) : jetBlockRow 2 65 w=rows0 w 237 := by
  change jetBlockRow 2 65 w=(1)*w 202 + (1)*w 244
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_237

theorem link0_238 (w : Fin 336→ℂ) : jetBlockRow 2 66 w=rows0 w 238 := by
  change jetBlockRow 2 66 w=(1)*w 205 + (1)*w 247
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_238

theorem link0_239 (w : Fin 336→ℂ) : jetBlockRow 2 67 w=rows0 w 239 := by
  change jetBlockRow 2 67 w=(1)*w 196 + (1)*w 224
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_239

theorem link0_240 (w : Fin 336→ℂ) : jetBlockRow 2 68 w=rows0 w 240 := by
  change jetBlockRow 2 68 w=(126)*w 0 + (126)*w 28 + (84)*w 84 + (84)*w 112 + (28)*w 168 + (28)*w 196 + (1)*w 197 + (1)*w 225
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_240

theorem link0_241 (w : Fin 336→ℂ) : jetBlockRow 2 69 w=rows0 w 241 := by
  change jetBlockRow 2 69 w=(126)*w 0 + (126)*w 56 + ((-84))*w 84 + ((-84))*w 140 + (28)*w 168 + (1)*w 195 + (1)*w 223 + (28)*w 224
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_241

theorem link0_242 (w : Fin 336→ℂ) : jetBlockRow 2 70 w=rows0 w 242 := by
  change jetBlockRow 2 70 w=(126)*w 14 + (126)*w 42 + (42)*w 98 + (42)*w 126 + (7)*w 182 + (1)*w 198 + (7)*w 210 + (1)*w 226
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_242

theorem link0_243 (w : Fin 336→ℂ) : jetBlockRow 2 71 w=rows0 w 243 := by
  change jetBlockRow 2 71 w=(126)*w 42 + (126)*w 70 + ((-42))*w 126 + ((-42))*w 154 + (1)*w 194 + (7)*w 210 + (1)*w 222 + (7)*w 238
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_243

theorem link0_244 (w : Fin 336→ℂ) : jetBlockRow 2 72 w=rows0 w 244 := by
  change jetBlockRow 2 72 w=(126)*w 21 + (126)*w 49 + (21)*w 105 + (21)*w 133 + (7/4)*w 189 + (1)*w 200 + (7/4)*w 217 + (1)*w 228
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_244

theorem link0_245 (w : Fin 336→ℂ) : jetBlockRow 2 73 w=rows0 w 245 := by
  change jetBlockRow 2 73 w=(126)*w 35 + (126)*w 63 + ((-21))*w 119 + ((-21))*w 147 + (1)*w 192 + (7/4)*w 203 + (1)*w 220 + (7/4)*w 231
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_245

theorem link0_246 (w : Fin 336→ℂ) : jetBlockRow 2 74 w=rows0 w 246 := by
  change jetBlockRow 2 74 w=(98)*w 0 + (98)*w 12 + (98)*w 24 + (98)*w 36 + (98)*w 60 + (98)*w 72 + (84)*w 84 + (84)*w 96 + (84)*w 108 + (84)*w 120 + (84)*w 144 + (84)*w 156 + (36)*w 168 + (36)*w 180 + (1)*w 181 + (36)*w 192 + (1)*w 193 + (36)*w 204 + (1)*w 205 + (1)*w 217 + (36)*w 228 + (1)*w 229 + (36)*w 240 + (1)*w 241
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_246

theorem link0_247 (w : Fin 336→ℂ) : jetBlockRow 2 75 w=rows0 w 247 := by
  change jetBlockRow 2 75 w=(98)*w 0 + (98)*w 12 + (98)*w 24 + (98)*w 48 + (98)*w 60 + (98)*w 72 + ((-84))*w 84 + ((-84))*w 96 + ((-84))*w 108 + ((-84))*w 132 + ((-84))*w 144 + ((-84))*w 156 + (36)*w 168 + (1)*w 179 + (36)*w 180 + (1)*w 191 + (36)*w 192 + (1)*w 203 + (1)*w 215 + (36)*w 216 + (1)*w 227 + (36)*w 228 + (1)*w 239 + (36)*w 240
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_247

theorem link0_248 (w : Fin 336→ℂ) : jetBlockRow 2 76 w=rows0 w 248 := by
  change jetBlockRow 2 76 w=(98)*w 6 + (98)*w 18 + (98)*w 30 + (98)*w 42 + (98)*w 54 + (98)*w 78 + (42)*w 90 + (42)*w 102 + (42)*w 114 + (42)*w 126 + (42)*w 138 + (42)*w 162 + (9)*w 174 + (1)*w 182 + (9)*w 186 + (1)*w 194 + (9)*w 198 + (1)*w 206 + (9)*w 210 + (1)*w 218 + (9)*w 222 + (1)*w 230 + (1)*w 242 + (9)*w 246
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_248

theorem link0_249 (w : Fin 336→ℂ) : jetBlockRow 2 77 w=rows0 w 249 := by
  change jetBlockRow 2 77 w=(1)*w 172 + (1)*w 176 + (1)*w 184 + (1)*w 188 + (1)*w 200 + (1)*w 208 + (1)*w 212 + (1)*w 220 + (1)*w 232 + (1)*w 236 + (1)*w 244 + (1)*w 248
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_249

theorem link0_250 (w : Fin 336→ℂ) : jetBlockRow 2 78 w=rows0 w 250 := by
  change jetBlockRow 2 78 w=(1)*w 171 + (10)*w 177 + (9)*w 195 + (1)*w 199 + (1)*w 227
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_250

theorem link0_251 (w : Fin 336→ℂ) : jetBlockRow 2 79 w=rows0 w 251 := by
  change jetBlockRow 2 79 w=(1)*w 173 + (10)*w 183 + (1)*w 201 + (9)*w 213 + (1)*w 229
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_251

theorem link0_252 (w : Fin 336→ℂ) : jetBlockRow 2 80 w=rows0 w 252 := by
  change jetBlockRow 2 80 w=(1)*w 174 + (10)*w 186 + (1)*w 202 + (9)*w 222 + (1)*w 230
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_252

theorem link0_253 (w : Fin 336→ℂ) : jetBlockRow 2 81 w=rows0 w 253 := by
  change jetBlockRow 2 81 w=(1)*w 177 + (10)*w 195 + (1)*w 205 + (1)*w 233 + (9)*w 249
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_253

theorem link0_254 (w : Fin 336→ℂ) : jetBlockRow 2 82 w=rows0 w 254 := by
  change jetBlockRow 2 82 w=(1)*w 221
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_254

theorem link0_255 (w : Fin 336→ℂ) : jetBlockRow 2 83 w=rows0 w 255 := by
  change jetBlockRow 2 83 w=(98)*w 0 + (98)*w 12 + (98)*w 24 + (98)*w 36 + (98)*w 48 + (98)*w 60 + (28)*w 84 + (28)*w 96 + (28)*w 108 + (28)*w 120 + (28)*w 132 + (28)*w 144 + (4)*w 168 + (4)*w 180 + (1)*w 183 + (4)*w 192 + (1)*w 195 + (4)*w 204 + (1)*w 207 + (4)*w 216 + (1)*w 219 + (4)*w 228 + (1)*w 231 + (1)*w 243
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_255

theorem link0_256 (w : Fin 336→ℂ) : jetBlockRow 2 84 w=rows0 w 256 := by
  change jetBlockRow 2 84 w=(1)*w 180 + (1)*w 192 + (1)*w 204 + (1)*w 216 + (1)*w 228 + (1)*w 240
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_256

theorem link0_257 (w : Fin 336→ℂ) : jetBlockRow 2 85 w=rows0 w 257 := by
  change jetBlockRow 2 85 w=(1)*w 176 + (10)*w 192 + (1)*w 204 + (1)*w 232 + (9)*w 240
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_257

theorem link0_258 (w : Fin 336→ℂ) : jetBlockRow 3 0 w=rows0 w 258 := by
  change jetBlockRow 3 0 w=((-28)/9)*w 82 + ((-2)/9)*w 166 + ((-2)/189)*w 250 + (1)*w 252 + ((-1)/3969)*w 334
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_258

theorem link0_259 (w : Fin 336→ℂ) : jetBlockRow 3 1 w=rows0 w 259 := by
  change jetBlockRow 3 1 w=(14/3)*w 81 + (1/2)*w 165 + (1/28)*w 249 + (1)*w 252 + (1/784)*w 333
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_259

theorem link0_260 (w : Fin 336→ℂ) : jetBlockRow 3 2 w=rows0 w 260 := by
  change jetBlockRow 3 2 w=(28/9)*w 82 + (2/9)*w 166 + (2/189)*w 250 + (1)*w 294 + (1/3969)*w 334
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_260

theorem link0_261 (w : Fin 336→ℂ) : jetBlockRow 3 3 w=rows0 w 261 := by
  change jetBlockRow 3 3 w=((-28)/3)*w 78 + ((-2))*w 162 + ((-2)/7)*w 246 + (1)*w 252 + ((-1)/49)*w 330
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_261

theorem link0_262 (w : Fin 336→ℂ) : jetBlockRow 3 4 w=rows0 w 262 := by
  change jetBlockRow 3 4 w=((-56)/9)*w 80 + ((-8)/9)*w 164 + ((-16)/189)*w 248 + (1)*w 273 + ((-16)/3969)*w 332
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_262

theorem link0_263 (w : Fin 336→ℂ) : jetBlockRow 3 5 w=rows0 w 263 := by
  change jetBlockRow 3 5 w=(1)*w 252
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_263

theorem link0_264 (w : Fin 336→ℂ) : jetBlockRow 3 6 w=rows0 w 264 := by
  change jetBlockRow 3 6 w=(392)*w 0 + (3528)*w 84 + (21168)*w 168 + (63504)*w 252 + (1)*w 253
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_264

theorem link0_265 (w : Fin 336→ℂ) : jetBlockRow 3 7 w=rows0 w 265 := by
  change jetBlockRow 3 7 w=(196)*w 42 + (882)*w 126 + (2646)*w 210 + (1)*w 254 + (3969)*w 294
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_265

theorem link0_266 (w : Fin 336→ℂ) : jetBlockRow 3 8 w=rows0 w 266 := by
  change jetBlockRow 3 8 w=(392/3)*w 0 + (392)*w 84 + (784)*w 168 + (784)*w 252 + (1)*w 255
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_266

theorem link0_267 (w : Fin 336→ℂ) : jetBlockRow 3 9 w=rows0 w 267 := by
  change jetBlockRow 3 9 w=(98)*w 21 + (441/2)*w 105 + (1323/4)*w 189 + (1)*w 256 + (3969/16)*w 273
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_267

theorem link0_268 (w : Fin 336→ℂ) : jetBlockRow 3 10 w=rows0 w 268 := by
  change jetBlockRow 3 10 w=(196/3)*w 42 + (98)*w 126 + (98)*w 210 + (1)*w 258 + (49)*w 294
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_268

theorem link0_269 (w : Fin 336→ℂ) : jetBlockRow 3 11 w=rows0 w 269 := by
  change jetBlockRow 3 11 w=(56)*w 48 + (72)*w 132 + (432/7)*w 216 + (1)*w 259 + (1296/49)*w 300
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_269

theorem link0_270 (w : Fin 336→ℂ) : jetBlockRow 3 12 w=rows0 w 270 := by
  change jetBlockRow 3 12 w=(392/9)*w 56 + (392/9)*w 140 + (784/27)*w 224 + (1)*w 261 + (784/81)*w 308
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_270

theorem link0_271 (w : Fin 336→ℂ) : jetBlockRow 3 13 w=rows0 w 271 := by
  change jetBlockRow 3 13 w=(98/3)*w 63 + (49/2)*w 147 + (49/4)*w 231 + (1)*w 264 + (49/16)*w 315
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_271

theorem link0_272 (w : Fin 336→ℂ) : jetBlockRow 3 14 w=rows0 w 272 := by
  change jetBlockRow 3 14 w=(28)*w 66 + (18)*w 150 + (54/7)*w 234 + (1)*w 266 + (81/49)*w 318
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_272

theorem link0_273 (w : Fin 336→ℂ) : jetBlockRow 3 15 w=rows0 w 273 := by
  change jetBlockRow 3 15 w=(196/9)*w 70 + (98/9)*w 154 + (98/27)*w 238 + (1)*w 270 + (49/81)*w 322
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_273

theorem link0_274 (w : Fin 336→ℂ) : jetBlockRow 3 16 w=rows0 w 274 := by
  change jetBlockRow 3 16 w=(56/3)*w 72 + (8)*w 156 + (16/7)*w 240 + (1)*w 273 + (16/49)*w 324
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_274

theorem link0_275 (w : Fin 336→ℂ) : jetBlockRow 3 17 w=rows0 w 275 := by
  change jetBlockRow 3 17 w=(14)*w 75 + (9/2)*w 159 + (27/28)*w 243 + (1)*w 280 + (81/784)*w 327
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_275

theorem link0_276 (w : Fin 336→ℂ) : jetBlockRow 3 18 w=rows0 w 276 := by
  change jetBlockRow 3 18 w=(98/9)*w 77 + (49/18)*w 161 + (49/108)*w 245 + (1)*w 288 + (49/1296)*w 329
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_276

theorem link0_277 (w : Fin 336→ℂ) : jetBlockRow 3 19 w=rows0 w 277 := by
  change jetBlockRow 3 19 w=(56/9)*w 80 + (8/9)*w 164 + (16/189)*w 248 + (1)*w 315 + (16/3969)*w 332
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_277

theorem link0_278 (w : Fin 336→ℂ) : jetBlockRow 3 20 w=rows0 w 278 := by
  change jetBlockRow 3 20 w=(98/9)*w 7 + ((-49)/18)*w 91 + (49/108)*w 175 + (1)*w 258 + ((-49)/1296)*w 259
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_278

theorem link0_279 (w : Fin 336→ℂ) : jetBlockRow 3 21 w=rows0 w 279 := by
  change jetBlockRow 3 21 w=(14)*w 9 + ((-9)/2)*w 93 + (27/28)*w 177 + ((-81)/784)*w 261 + (1)*w 266
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_279

theorem link0_280 (w : Fin 336→ℂ) : jetBlockRow 3 22 w=rows0 w 280 := by
  change jetBlockRow 3 22 w=(196/9)*w 14 + ((-98)/9)*w 98 + (98/27)*w 182 + ((-49)/81)*w 266 + (1)*w 276
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_280

theorem link0_281 (w : Fin 336→ℂ) : jetBlockRow 3 23 w=rows0 w 281 := by
  change jetBlockRow 3 23 w=(28)*w 18 + ((-18))*w 102 + (54/7)*w 186 + ((-81)/49)*w 270 + (1)*w 280
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_281

theorem link0_282 (w : Fin 336→ℂ) : jetBlockRow 3 24 w=rows0 w 282 := by
  change jetBlockRow 3 24 w=(98/3)*w 21 + ((-49)/2)*w 105 + (49/4)*w 189 + ((-49)/16)*w 273 + (1)*w 282
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_282

theorem link0_283 (w : Fin 336→ℂ) : jetBlockRow 3 25 w=rows0 w 283 := by
  change jetBlockRow 3 25 w=(392/9)*w 28 + ((-392)/9)*w 112 + (784/27)*w 196 + ((-784)/81)*w 280 + (1)*w 285
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_283

theorem link0_284 (w : Fin 336→ℂ) : jetBlockRow 3 26 w=rows0 w 284 := by
  change jetBlockRow 3 26 w=(56)*w 36 + ((-72))*w 120 + (432/7)*w 204 + (1)*w 287 + ((-1296)/49)*w 288
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_284

theorem link0_285 (w : Fin 336→ℂ) : jetBlockRow 3 27 w=rows0 w 285 := by
  change jetBlockRow 3 27 w=(196/3)*w 42 + ((-98))*w 126 + (98)*w 210 + (1)*w 288 + ((-49))*w 294
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_285

theorem link0_286 (w : Fin 336→ℂ) : jetBlockRow 3 28 w=rows0 w 286 := by
  change jetBlockRow 3 28 w=(98)*w 63 + ((-441)/2)*w 147 + (1323/4)*w 231 + (1)*w 290 + ((-3969)/16)*w 315
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_286

theorem link0_287 (w : Fin 336→ℂ) : jetBlockRow 3 29 w=rows0 w 287 := by
  change jetBlockRow 3 29 w=(392/3)*w 0 + ((-392))*w 84 + (784)*w 168 + ((-784))*w 252 + (1)*w 291
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_287

theorem link0_288 (w : Fin 336→ℂ) : jetBlockRow 3 30 w=rows0 w 288 := by
  change jetBlockRow 3 30 w=(196)*w 42 + ((-882))*w 126 + (2646)*w 210 + (1)*w 292 + ((-3969))*w 294
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_288

theorem link0_289 (w : Fin 336→ℂ) : jetBlockRow 3 31 w=rows0 w 289 := by
  change jetBlockRow 3 31 w=(392)*w 0 + ((-3528))*w 84 + (21168)*w 168 + ((-63504))*w 252 + (1)*w 293
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_289

theorem link0_290 (w : Fin 336→ℂ) : jetBlockRow 3 32 w=rows0 w 290 := by
  change jetBlockRow 3 32 w=((-392))*w 0 + ((-3528))*w 84 + ((-21168))*w 168 + ((-63504))*w 252 + (1)*w 295
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_290

theorem link0_291 (w : Fin 336→ℂ) : jetBlockRow 3 33 w=rows0 w 291 := by
  change jetBlockRow 3 33 w=((-196))*w 42 + ((-882))*w 126 + ((-2646))*w 210 + ((-3969))*w 294 + (1)*w 296
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_291

theorem link0_292 (w : Fin 336→ℂ) : jetBlockRow 3 34 w=rows0 w 292 := by
  change jetBlockRow 3 34 w=((-392)/3)*w 0 + ((-392))*w 84 + ((-784))*w 168 + ((-784))*w 252 + (1)*w 297
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_292

theorem link0_293 (w : Fin 336→ℂ) : jetBlockRow 3 35 w=rows0 w 293 := by
  change jetBlockRow 3 35 w=((-98))*w 21 + ((-441)/2)*w 105 + ((-1323)/4)*w 189 + ((-3969)/16)*w 273 + (1)*w 298
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_293

theorem link0_294 (w : Fin 336→ℂ) : jetBlockRow 3 36 w=rows0 w 294 := by
  change jetBlockRow 3 36 w=((-56))*w 48 + ((-72))*w 132 + ((-432)/7)*w 216 + ((-1296)/49)*w 300 + (1)*w 301
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_294

theorem link0_295 (w : Fin 336→ℂ) : jetBlockRow 3 37 w=rows0 w 295 := by
  change jetBlockRow 3 37 w=((-392)/9)*w 56 + ((-392)/9)*w 140 + ((-784)/27)*w 224 + (1)*w 303 + ((-784)/81)*w 308
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_295

theorem link0_296 (w : Fin 336→ℂ) : jetBlockRow 3 38 w=rows0 w 296 := by
  change jetBlockRow 3 38 w=((-98)/3)*w 63 + ((-49)/2)*w 147 + ((-49)/4)*w 231 + (1)*w 306 + ((-49)/16)*w 315
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_296

theorem link0_297 (w : Fin 336→ℂ) : jetBlockRow 3 39 w=rows0 w 297 := by
  change jetBlockRow 3 39 w=((-196)/9)*w 70 + ((-98)/9)*w 154 + ((-98)/27)*w 238 + (1)*w 312 + ((-49)/81)*w 322
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_297

theorem link0_298 (w : Fin 336→ℂ) : jetBlockRow 3 40 w=rows0 w 298 := by
  change jetBlockRow 3 40 w=((-392))*w 0 + (3528)*w 84 + ((-21168))*w 168 + (63504)*w 252 + (1)*w 335
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_298

theorem link0_299 (w : Fin 336→ℂ) : jetBlockRow 3 41 w=rows0 w 299 := by
  change jetBlockRow 3 41 w=((-686)/9)*w 79 + (49/18)*w 163 + ((-7)/108)*w 247 + (1)*w 306 + (1/1296)*w 331
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_299

theorem link0_300 (w : Fin 336→ℂ) : jetBlockRow 3 42 w=rows0 w 300 := by
  change jetBlockRow 3 42 w=((-1372)/9)*w 8 + (98/9)*w 92 + ((-14)/27)*w 176 + (1/81)*w 260 + (1)*w 312
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_300

theorem link0_301 (w : Fin 336→ℂ) : jetBlockRow 3 43 w=rows0 w 301 := by
  change jetBlockRow 3 43 w=((-2744)/9)*w 10 + (392/9)*w 94 + ((-112)/27)*w 178 + (16/81)*w 262 + (1)*w 321
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_301

theorem link0_302 (w : Fin 336→ℂ) : jetBlockRow 3 44 w=rows0 w 302 := by
  change jetBlockRow 3 44 w=((-686))*w 15 + (441/2)*w 99 + ((-189)/4)*w 183 + (81/16)*w 267 + (1)*w 326
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_302

theorem link0_303 (w : Fin 336→ℂ) : jetBlockRow 3 45 w=rows0 w 303 := by
  change jetBlockRow 3 45 w=((-1372))*w 24 + (882)*w 108 + ((-378))*w 192 + (81)*w 276 + (1)*w 328
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_303

theorem link0_304 (w : Fin 336→ℂ) : jetBlockRow 3 46 w=rows0 w 304 := by
  change jetBlockRow 3 46 w=((-2744))*w 30 + (3528)*w 114 + ((-3024))*w 198 + (1)*w 257 + (1296)*w 282
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_304

theorem link0_305 (w : Fin 336→ℂ) : jetBlockRow 3 47 w=rows0 w 305 := by
  change jetBlockRow 3 47 w=(1)*w 257 + (1)*w 299
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_305

theorem link0_306 (w : Fin 336→ℂ) : jetBlockRow 3 48 w=rows0 w 306 := by
  change jetBlockRow 3 48 w=(1)*w 260 + (1)*w 302
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_306

theorem link0_307 (w : Fin 336→ℂ) : jetBlockRow 3 49 w=rows0 w 307 := by
  change jetBlockRow 3 49 w=(1)*w 262 + (1)*w 304
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_307

theorem link0_308 (w : Fin 336→ℂ) : jetBlockRow 3 50 w=rows0 w 308 := by
  change jetBlockRow 3 50 w=(1)*w 263 + (1)*w 305
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_308

theorem link0_309 (w : Fin 336→ℂ) : jetBlockRow 3 51 w=rows0 w 309 := by
  change jetBlockRow 3 51 w=(1)*w 265 + (1)*w 307
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_309

theorem link0_310 (w : Fin 336→ℂ) : jetBlockRow 3 52 w=rows0 w 310 := by
  change jetBlockRow 3 52 w=(1)*w 267 + (1)*w 309
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_310

theorem link0_311 (w : Fin 336→ℂ) : jetBlockRow 3 53 w=rows0 w 311 := by
  change jetBlockRow 3 53 w=(1)*w 268 + (1)*w 310
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_311

theorem link0_312 (w : Fin 336→ℂ) : jetBlockRow 3 54 w=rows0 w 312 := by
  change jetBlockRow 3 54 w=(1)*w 269 + (1)*w 311
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_312

theorem link0_313 (w : Fin 336→ℂ) : jetBlockRow 3 55 w=rows0 w 313 := by
  change jetBlockRow 3 55 w=(1)*w 271 + (1)*w 313
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_313

theorem link0_314 (w : Fin 336→ℂ) : jetBlockRow 3 56 w=rows0 w 314 := by
  change jetBlockRow 3 56 w=(1)*w 272 + (1)*w 314
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_314

theorem link0_315 (w : Fin 336→ℂ) : jetBlockRow 3 57 w=rows0 w 315 := by
  change jetBlockRow 3 57 w=(1)*w 274 + (1)*w 316
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_315

theorem link0_316 (w : Fin 336→ℂ) : jetBlockRow 3 58 w=rows0 w 316 := by
  change jetBlockRow 3 58 w=(1)*w 275 + (1)*w 317
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_316

theorem link0_317 (w : Fin 336→ℂ) : jetBlockRow 3 59 w=rows0 w 317 := by
  change jetBlockRow 3 59 w=(1)*w 277 + (1)*w 319
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_317

theorem link0_318 (w : Fin 336→ℂ) : jetBlockRow 3 60 w=rows0 w 318 := by
  change jetBlockRow 3 60 w=(1)*w 278 + (1)*w 320
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_318

theorem link0_319 (w : Fin 336→ℂ) : jetBlockRow 3 61 w=rows0 w 319 := by
  change jetBlockRow 3 61 w=(1)*w 279 + (1)*w 321
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_319

theorem link0_320 (w : Fin 336→ℂ) : jetBlockRow 3 62 w=rows0 w 320 := by
  change jetBlockRow 3 62 w=(1)*w 281 + (1)*w 323
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_320

theorem link0_321 (w : Fin 336→ℂ) : jetBlockRow 3 63 w=rows0 w 321 := by
  change jetBlockRow 3 63 w=(1)*w 283 + (1)*w 325
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_321

theorem link0_322 (w : Fin 336→ℂ) : jetBlockRow 3 64 w=rows0 w 322 := by
  change jetBlockRow 3 64 w=(1)*w 284 + (1)*w 326
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_322

theorem link0_323 (w : Fin 336→ℂ) : jetBlockRow 3 65 w=rows0 w 323 := by
  change jetBlockRow 3 65 w=(1)*w 286 + (1)*w 328
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_323

theorem link0_324 (w : Fin 336→ℂ) : jetBlockRow 3 66 w=rows0 w 324 := by
  change jetBlockRow 3 66 w=(1)*w 289 + (1)*w 331
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_324

theorem link0_325 (w : Fin 336→ℂ) : jetBlockRow 3 67 w=rows0 w 325 := by
  change jetBlockRow 3 67 w=(1)*w 280 + (1)*w 308
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_325

theorem link0_326 (w : Fin 336→ℂ) : jetBlockRow 3 68 w=rows0 w 326 := by
  change jetBlockRow 3 68 w=(3528)*w 0 + (3528)*w 28 + (3528)*w 84 + (3528)*w 112 + (2352)*w 168 + (2352)*w 196 + (784)*w 252 + (784)*w 280 + (1)*w 281 + (1)*w 309
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_326

theorem link0_327 (w : Fin 336→ℂ) : jetBlockRow 3 69 w=rows0 w 327 := by
  change jetBlockRow 3 69 w=((-3528))*w 0 + ((-3528))*w 56 + (3528)*w 84 + (3528)*w 140 + ((-2352))*w 168 + ((-2352))*w 224 + (784)*w 252 + (1)*w 279 + (1)*w 307 + (784)*w 308
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_327

theorem link0_328 (w : Fin 336→ℂ) : jetBlockRow 3 70 w=rows0 w 328 := by
  change jetBlockRow 3 70 w=(1764)*w 14 + (1764)*w 42 + (882)*w 98 + (882)*w 126 + (294)*w 182 + (294)*w 210 + (49)*w 266 + (1)*w 282 + (49)*w 294 + (1)*w 310
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_328

theorem link0_329 (w : Fin 336→ℂ) : jetBlockRow 3 71 w=rows0 w 329 := by
  change jetBlockRow 3 71 w=((-1764))*w 42 + ((-1764))*w 70 + (882)*w 126 + (882)*w 154 + ((-294))*w 210 + ((-294))*w 238 + (1)*w 278 + (49)*w 294 + (1)*w 306 + (49)*w 322
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_329

theorem link0_330 (w : Fin 336→ℂ) : jetBlockRow 3 72 w=rows0 w 330 := by
  change jetBlockRow 3 72 w=(882)*w 21 + (882)*w 49 + (441/2)*w 105 + (441/2)*w 133 + (147/4)*w 189 + (147/4)*w 217 + (49/16)*w 273 + (1)*w 284 + (49/16)*w 301 + (1)*w 312
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_330

theorem link0_331 (w : Fin 336→ℂ) : jetBlockRow 3 73 w=rows0 w 331 := by
  change jetBlockRow 3 73 w=((-882))*w 35 + ((-882))*w 63 + (441/2)*w 119 + (441/2)*w 147 + ((-147)/4)*w 203 + ((-147)/4)*w 231 + (1)*w 276 + (49/16)*w 287 + (1)*w 304 + (49/16)*w 315
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_331

theorem link0_332 (w : Fin 336→ℂ) : jetBlockRow 3 74 w=rows0 w 332 := by
  change jetBlockRow 3 74 w=(2744)*w 0 + (2744)*w 12 + (2744)*w 24 + (2744)*w 36 + (2744)*w 60 + (2744)*w 72 + (3528)*w 84 + (3528)*w 96 + (3528)*w 108 + (3528)*w 120 + (3528)*w 144 + (3528)*w 156 + (3024)*w 168 + (3024)*w 180 + (3024)*w 192 + (3024)*w 204 + (3024)*w 228 + (3024)*w 240 + (1296)*w 252 + (1296)*w 264 + (1)*w 265 + (1296)*w 276 + (1)*w 277 + (1296)*w 288 + (1)*w 289 + (1)*w 301 + (1296)*w 312 + (1)*w 313 + (1296)*w 324 + (1)*w 325
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_332

theorem link0_333 (w : Fin 336→ℂ) : jetBlockRow 3 75 w=rows0 w 333 := by
  change jetBlockRow 3 75 w=((-2744))*w 0 + ((-2744))*w 12 + ((-2744))*w 24 + ((-2744))*w 48 + ((-2744))*w 60 + ((-2744))*w 72 + (3528)*w 84 + (3528)*w 96 + (3528)*w 108 + (3528)*w 132 + (3528)*w 144 + (3528)*w 156 + ((-3024))*w 168 + ((-3024))*w 180 + ((-3024))*w 192 + ((-3024))*w 216 + ((-3024))*w 228 + ((-3024))*w 240 + (1296)*w 252 + (1)*w 263 + (1296)*w 264 + (1)*w 275 + (1296)*w 276 + (1)*w 287 + (1)*w 299 + (1296)*w 300 + (1)*w 311 + (1296)*w 312 + (1)*w 323 + (1296)*w 324
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_333

theorem link0_334 (w : Fin 336→ℂ) : jetBlockRow 3 76 w=rows0 w 334 := by
  change jetBlockRow 3 76 w=(1372)*w 6 + (1372)*w 18 + (1372)*w 30 + (1372)*w 42 + (1372)*w 54 + (1372)*w 78 + (882)*w 90 + (882)*w 102 + (882)*w 114 + (882)*w 126 + (882)*w 138 + (882)*w 162 + (378)*w 174 + (378)*w 186 + (378)*w 198 + (378)*w 210 + (378)*w 222 + (378)*w 246 + (81)*w 258 + (1)*w 266 + (81)*w 270 + (1)*w 278 + (81)*w 282 + (1)*w 290 + (81)*w 294 + (1)*w 302 + (81)*w 306 + (1)*w 314 + (1)*w 326 + (81)*w 330
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_334

theorem link0_335 (w : Fin 336→ℂ) : jetBlockRow 3 77 w=rows0 w 335 := by
  change jetBlockRow 3 77 w=(1)*w 256 + (1)*w 260 + (1)*w 268 + (1)*w 272 + (1)*w 284 + (1)*w 292 + (1)*w 296 + (1)*w 304 + (1)*w 316 + (1)*w 320 + (1)*w 328 + (1)*w 332
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_335

theorem link0_336 (w : Fin 336→ℂ) : jetBlockRow 3 78 w=rows0 w 336 := by
  change jetBlockRow 3 78 w=(1)*w 255 + (30)*w 261 + (81)*w 279 + (1)*w 283 + (1)*w 311
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_336

theorem link0_337 (w : Fin 336→ℂ) : jetBlockRow 3 79 w=rows0 w 337 := by
  change jetBlockRow 3 79 w=(1)*w 257 + (30)*w 267 + (1)*w 285 + (81)*w 297 + (1)*w 313
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_337

theorem link0_338 (w : Fin 336→ℂ) : jetBlockRow 3 80 w=rows0 w 338 := by
  change jetBlockRow 3 80 w=(1)*w 258 + (30)*w 270 + (1)*w 286 + (81)*w 306 + (1)*w 314
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_338

theorem link0_339 (w : Fin 336→ℂ) : jetBlockRow 3 81 w=rows0 w 339 := by
  change jetBlockRow 3 81 w=(1)*w 261 + (30)*w 279 + (1)*w 289 + (1)*w 317 + (81)*w 333
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_339

theorem link0_340 (w : Fin 336→ℂ) : jetBlockRow 3 82 w=rows0 w 340 := by
  change jetBlockRow 3 82 w=(1)*w 305
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_340

theorem link0_341 (w : Fin 336→ℂ) : jetBlockRow 3 83 w=rows0 w 341 := by
  change jetBlockRow 3 83 w=(2744/3)*w 0 + (2744/3)*w 12 + (2744/3)*w 24 + (2744/3)*w 36 + (2744/3)*w 48 + (2744/3)*w 60 + (392)*w 84 + (392)*w 96 + (392)*w 108 + (392)*w 120 + (392)*w 132 + (392)*w 144 + (112)*w 168 + (112)*w 180 + (112)*w 192 + (112)*w 204 + (112)*w 216 + (112)*w 228 + (16)*w 252 + (16)*w 264 + (1)*w 267 + (16)*w 276 + (1)*w 279 + (16)*w 288 + (1)*w 291 + (16)*w 300 + (1)*w 303 + (16)*w 312 + (1)*w 315 + (1)*w 327
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_341

theorem link0_342 (w : Fin 336→ℂ) : jetBlockRow 3 84 w=rows0 w 342 := by
  change jetBlockRow 3 84 w=(1)*w 264 + (1)*w 276 + (1)*w 288 + (1)*w 300 + (1)*w 312 + (1)*w 324
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_342

theorem link0_343 (w : Fin 336→ℂ) : jetBlockRow 3 85 w=rows0 w 343 := by
  change jetBlockRow 3 85 w=(1)*w 260 + (30)*w 276 + (1)*w 288 + (1)*w 316 + (81)*w 324
  norm_num [jetBlockRow,jetSlice,finProdFinEquiv,lowerIndex,leadingRows,positiveTaylorRows,Finset.sum_range_succ]
  <;> ring

#print axioms link0_343

end SmallLevelTwentyEightJetBlock
end
end
