module
public import SmallLevelTwentySixIntegerRow87ColumnFiveTheoryV4
public import SmallLevelTwentySixIntegerRow89ColumnFiveTheoryV4
public import SmallLevelTwentySixIntegerRow87ColumnFourTheoryV4
public import SmallLevelTwentySixIntegerRow89ColumnFourTheoryV4
public import SmallLevelTwentySixIntegerRow87ColumnOneTheoryV4
public import SmallLevelTwentySixIntegerRow89ColumnOneTheoryV4
public import SmallLevelTwentySixIntegerRow87ColumnThreeTheoryV4
public import SmallLevelTwentySixIntegerRow89ColumnThreeTheoryV4
public import SmallLevelTwentySixIntegerRow87ColumnTwoTheoryV4
public import SmallLevelTwentySixIntegerRow89ColumnTwoTheoryV4
public import SmallLevelTwentySixIntegerRow87ColumnZeroTheoryV4
public import SmallLevelTwentySixIntegerRow89ColumnZeroTheoryV4
public import SmallLevelTwentySixIntegerRowIndexTransposeSourcesSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixIntegerRow87Transpose
open QuantitativeArithmeticIntegerSevenLaurentRows

theorem column0_operation : SmallLevelTwentySixIntegerRow87ColumnZero.operationData.Perm
    (column inputs (List.range 5) 0++[(-1,5,(0,0,0,0,0,0,0))]) := by decide +kernel

theorem column0_output : (SmallLevelTwentySixIntegerRow87ColumnZero.inputs 5).Perm (columnPiece 0 0 outputData) := by decide +kernel

theorem column0_weights : ∀ i : Fin 5,SmallLevelTwentySixIntegerRow87ColumnZero.inputs i=weights i := by decide +kernel

theorem column0_eval (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun k => if k=0 then 1 else 0) outputData=
      eval x y z w a b c (weightValue x y z w a b c) (column inputs (List.range 5) 0) := by
  have h:=SmallLevelTwentySixIntegerRow87ColumnZero.column_certificate x y z w a b c hx hy hz hw
  rw [SmallLevelIntegerLaurentColumnOutput.eval_perm x y z w a b c _ column0_operation] at h
  have hh:=SmallLevelIntegerLaurentColumnOutput.column_output x y z w a b c inputs
    SmallLevelTwentySixIntegerRow87ColumnZero.inputs outputData 5 0 column0_output h
  rw [hh]
  simp only [SmallLevelIntegerLaurentColumnOutput.eval_column_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hb:=column0_weights ⟨i,List.mem_range.mp hi⟩
  change _=weightValue x y z w a b c i*_
  rw [hb]
  rfl

#print axioms column0_eval

theorem column1_operation : SmallLevelTwentySixIntegerRow87ColumnOne.operationData.Perm
    (column inputs (List.range 5) 1++[(-1,5,(0,0,0,0,0,0,0))]) := by decide +kernel

theorem column1_output : (SmallLevelTwentySixIntegerRow87ColumnOne.inputs 5).Perm (columnPiece 0 1 outputData) := by decide +kernel

theorem column1_weights : ∀ i : Fin 5,SmallLevelTwentySixIntegerRow87ColumnOne.inputs i=weights i := by decide +kernel

theorem column1_eval (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun k => if k=1 then 1 else 0) outputData=
      eval x y z w a b c (weightValue x y z w a b c) (column inputs (List.range 5) 1) := by
  have h:=SmallLevelTwentySixIntegerRow87ColumnOne.column_certificate x y z w a b c hx hy hz hw
  rw [SmallLevelIntegerLaurentColumnOutput.eval_perm x y z w a b c _ column1_operation] at h
  have hh:=SmallLevelIntegerLaurentColumnOutput.column_output x y z w a b c inputs
    SmallLevelTwentySixIntegerRow87ColumnOne.inputs outputData 5 1 column1_output h
  rw [hh]
  simp only [SmallLevelIntegerLaurentColumnOutput.eval_column_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hb:=column1_weights ⟨i,List.mem_range.mp hi⟩
  change _=weightValue x y z w a b c i*_
  rw [hb]
  rfl

#print axioms column1_eval

theorem column2_operation : SmallLevelTwentySixIntegerRow87ColumnTwo.operationData.Perm
    (column inputs (List.range 5) 2++[(-1,5,(0,0,0,0,0,0,0))]) := by decide +kernel

theorem column2_output : (SmallLevelTwentySixIntegerRow87ColumnTwo.inputs 5).Perm (columnPiece 0 2 outputData) := by decide +kernel

theorem column2_weights : ∀ i : Fin 5,SmallLevelTwentySixIntegerRow87ColumnTwo.inputs i=weights i := by decide +kernel

theorem column2_eval (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun k => if k=2 then 1 else 0) outputData=
      eval x y z w a b c (weightValue x y z w a b c) (column inputs (List.range 5) 2) := by
  have h:=SmallLevelTwentySixIntegerRow87ColumnTwo.column_certificate x y z w a b c hx hy hz hw
  rw [SmallLevelIntegerLaurentColumnOutput.eval_perm x y z w a b c _ column2_operation] at h
  have hh:=SmallLevelIntegerLaurentColumnOutput.column_output x y z w a b c inputs
    SmallLevelTwentySixIntegerRow87ColumnTwo.inputs outputData 5 2 column2_output h
  rw [hh]
  simp only [SmallLevelIntegerLaurentColumnOutput.eval_column_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hb:=column2_weights ⟨i,List.mem_range.mp hi⟩
  change _=weightValue x y z w a b c i*_
  rw [hb]
  rfl

#print axioms column2_eval

theorem column3_operation : SmallLevelTwentySixIntegerRow87ColumnThree.operationData.Perm
    (column inputs (List.range 5) 3++[(-1,5,(0,0,0,0,0,0,0))]) := by decide +kernel

theorem column3_output : (SmallLevelTwentySixIntegerRow87ColumnThree.inputs 5).Perm (columnPiece 0 3 outputData) := by decide +kernel

theorem column3_weights : ∀ i : Fin 5,SmallLevelTwentySixIntegerRow87ColumnThree.inputs i=weights i := by decide +kernel

theorem column3_eval (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun k => if k=3 then 1 else 0) outputData=
      eval x y z w a b c (weightValue x y z w a b c) (column inputs (List.range 5) 3) := by
  have h:=SmallLevelTwentySixIntegerRow87ColumnThree.column_certificate x y z w a b c hx hy hz hw
  rw [SmallLevelIntegerLaurentColumnOutput.eval_perm x y z w a b c _ column3_operation] at h
  have hh:=SmallLevelIntegerLaurentColumnOutput.column_output x y z w a b c inputs
    SmallLevelTwentySixIntegerRow87ColumnThree.inputs outputData 5 3 column3_output h
  rw [hh]
  simp only [SmallLevelIntegerLaurentColumnOutput.eval_column_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hb:=column3_weights ⟨i,List.mem_range.mp hi⟩
  change _=weightValue x y z w a b c i*_
  rw [hb]
  rfl

#print axioms column3_eval

theorem column4_operation : SmallLevelTwentySixIntegerRow87ColumnFour.operationData.Perm
    (column inputs (List.range 5) 4++[(-1,5,(0,0,0,0,0,0,0))]) := by decide +kernel

theorem column4_output : (SmallLevelTwentySixIntegerRow87ColumnFour.inputs 5).Perm (columnPiece 0 4 outputData) := by decide +kernel

theorem column4_weights : ∀ i : Fin 5,SmallLevelTwentySixIntegerRow87ColumnFour.inputs i=weights i := by decide +kernel

theorem column4_eval (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun k => if k=4 then 1 else 0) outputData=
      eval x y z w a b c (weightValue x y z w a b c) (column inputs (List.range 5) 4) := by
  have h:=SmallLevelTwentySixIntegerRow87ColumnFour.column_certificate x y z w a b c hx hy hz hw
  rw [SmallLevelIntegerLaurentColumnOutput.eval_perm x y z w a b c _ column4_operation] at h
  have hh:=SmallLevelIntegerLaurentColumnOutput.column_output x y z w a b c inputs
    SmallLevelTwentySixIntegerRow87ColumnFour.inputs outputData 5 4 column4_output h
  rw [hh]
  simp only [SmallLevelIntegerLaurentColumnOutput.eval_column_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hb:=column4_weights ⟨i,List.mem_range.mp hi⟩
  change _=weightValue x y z w a b c i*_
  rw [hb]
  rfl

#print axioms column4_eval

theorem column5_operation : SmallLevelTwentySixIntegerRow87ColumnFive.operationData.Perm
    (column inputs (List.range 5) 5++[(-1,5,(0,0,0,0,0,0,0))]) := by decide +kernel

theorem column5_output : (SmallLevelTwentySixIntegerRow87ColumnFive.inputs 5).Perm (columnPiece 0 5 outputData) := by decide +kernel

theorem column5_weights : ∀ i : Fin 5,SmallLevelTwentySixIntegerRow87ColumnFive.inputs i=weights i := by decide +kernel

theorem column5_eval (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun k => if k=5 then 1 else 0) outputData=
      eval x y z w a b c (weightValue x y z w a b c) (column inputs (List.range 5) 5) := by
  have h:=SmallLevelTwentySixIntegerRow87ColumnFive.column_certificate x y z w a b c hx hy hz hw
  rw [SmallLevelIntegerLaurentColumnOutput.eval_perm x y z w a b c _ column5_operation] at h
  have hh:=SmallLevelIntegerLaurentColumnOutput.column_output x y z w a b c inputs
    SmallLevelTwentySixIntegerRow87ColumnFive.inputs outputData 5 5 column5_output h
  rw [hh]
  simp only [SmallLevelIntegerLaurentColumnOutput.eval_column_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hb:=column5_weights ⟨i,List.mem_range.mp hi⟩
  change _=weightValue x y z w a b c i*_
  rw [hb]
  rfl

#print axioms column5_eval

end SmallLevelTwentySixIntegerRow87Transpose
end

section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixIntegerRow89Transpose
open QuantitativeArithmeticIntegerSevenLaurentRows

theorem column0_operation : SmallLevelTwentySixIntegerRow89ColumnZero.operationData.Perm
    (column inputs (List.range 5) 0++[(-1,5,(0,0,0,0,0,0,0))]) := by decide +kernel

theorem column0_output : (SmallLevelTwentySixIntegerRow89ColumnZero.inputs 5).Perm (columnPiece 0 0 outputData) := by decide +kernel

theorem column0_weights : ∀ i : Fin 5,SmallLevelTwentySixIntegerRow89ColumnZero.inputs i=weights i := by decide +kernel

theorem column0_eval (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun k => if k=0 then 1 else 0) outputData=
      eval x y z w a b c (weightValue x y z w a b c) (column inputs (List.range 5) 0) := by
  have h:=SmallLevelTwentySixIntegerRow89ColumnZero.column_certificate x y z w a b c hx hy hz hw
  rw [SmallLevelIntegerLaurentColumnOutput.eval_perm x y z w a b c _ column0_operation] at h
  have hh:=SmallLevelIntegerLaurentColumnOutput.column_output x y z w a b c inputs
    SmallLevelTwentySixIntegerRow89ColumnZero.inputs outputData 5 0 column0_output h
  rw [hh]
  simp only [SmallLevelIntegerLaurentColumnOutput.eval_column_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hb:=column0_weights ⟨i,List.mem_range.mp hi⟩
  change _=weightValue x y z w a b c i*_
  rw [hb]
  rfl

#print axioms column0_eval

theorem column1_operation : SmallLevelTwentySixIntegerRow89ColumnOne.operationData.Perm
    (column inputs (List.range 5) 1++[(-1,5,(0,0,0,0,0,0,0))]) := by decide +kernel

theorem column1_output : (SmallLevelTwentySixIntegerRow89ColumnOne.inputs 5).Perm (columnPiece 0 1 outputData) := by decide +kernel

theorem column1_weights : ∀ i : Fin 5,SmallLevelTwentySixIntegerRow89ColumnOne.inputs i=weights i := by decide +kernel

theorem column1_eval (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun k => if k=1 then 1 else 0) outputData=
      eval x y z w a b c (weightValue x y z w a b c) (column inputs (List.range 5) 1) := by
  have h:=SmallLevelTwentySixIntegerRow89ColumnOne.column_certificate x y z w a b c hx hy hz hw
  rw [SmallLevelIntegerLaurentColumnOutput.eval_perm x y z w a b c _ column1_operation] at h
  have hh:=SmallLevelIntegerLaurentColumnOutput.column_output x y z w a b c inputs
    SmallLevelTwentySixIntegerRow89ColumnOne.inputs outputData 5 1 column1_output h
  rw [hh]
  simp only [SmallLevelIntegerLaurentColumnOutput.eval_column_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hb:=column1_weights ⟨i,List.mem_range.mp hi⟩
  change _=weightValue x y z w a b c i*_
  rw [hb]
  rfl

#print axioms column1_eval

theorem column2_operation : SmallLevelTwentySixIntegerRow89ColumnTwo.operationData.Perm
    (column inputs (List.range 5) 2++[(-1,5,(0,0,0,0,0,0,0))]) := by decide +kernel

theorem column2_output : (SmallLevelTwentySixIntegerRow89ColumnTwo.inputs 5).Perm (columnPiece 0 2 outputData) := by decide +kernel

theorem column2_weights : ∀ i : Fin 5,SmallLevelTwentySixIntegerRow89ColumnTwo.inputs i=weights i := by decide +kernel

theorem column2_eval (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun k => if k=2 then 1 else 0) outputData=
      eval x y z w a b c (weightValue x y z w a b c) (column inputs (List.range 5) 2) := by
  have h:=SmallLevelTwentySixIntegerRow89ColumnTwo.column_certificate x y z w a b c hx hy hz hw
  rw [SmallLevelIntegerLaurentColumnOutput.eval_perm x y z w a b c _ column2_operation] at h
  have hh:=SmallLevelIntegerLaurentColumnOutput.column_output x y z w a b c inputs
    SmallLevelTwentySixIntegerRow89ColumnTwo.inputs outputData 5 2 column2_output h
  rw [hh]
  simp only [SmallLevelIntegerLaurentColumnOutput.eval_column_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hb:=column2_weights ⟨i,List.mem_range.mp hi⟩
  change _=weightValue x y z w a b c i*_
  rw [hb]
  rfl

#print axioms column2_eval

theorem column3_operation : SmallLevelTwentySixIntegerRow89ColumnThree.operationData.Perm
    (column inputs (List.range 5) 3++[(-1,5,(0,0,0,0,0,0,0))]) := by decide +kernel

theorem column3_output : (SmallLevelTwentySixIntegerRow89ColumnThree.inputs 5).Perm (columnPiece 0 3 outputData) := by decide +kernel

theorem column3_weights : ∀ i : Fin 5,SmallLevelTwentySixIntegerRow89ColumnThree.inputs i=weights i := by decide +kernel

theorem column3_eval (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun k => if k=3 then 1 else 0) outputData=
      eval x y z w a b c (weightValue x y z w a b c) (column inputs (List.range 5) 3) := by
  have h:=SmallLevelTwentySixIntegerRow89ColumnThree.column_certificate x y z w a b c hx hy hz hw
  rw [SmallLevelIntegerLaurentColumnOutput.eval_perm x y z w a b c _ column3_operation] at h
  have hh:=SmallLevelIntegerLaurentColumnOutput.column_output x y z w a b c inputs
    SmallLevelTwentySixIntegerRow89ColumnThree.inputs outputData 5 3 column3_output h
  rw [hh]
  simp only [SmallLevelIntegerLaurentColumnOutput.eval_column_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hb:=column3_weights ⟨i,List.mem_range.mp hi⟩
  change _=weightValue x y z w a b c i*_
  rw [hb]
  rfl

#print axioms column3_eval

theorem column4_operation : SmallLevelTwentySixIntegerRow89ColumnFour.operationData.Perm
    (column inputs (List.range 5) 4++[(-1,5,(0,0,0,0,0,0,0))]) := by decide +kernel

theorem column4_output : (SmallLevelTwentySixIntegerRow89ColumnFour.inputs 5).Perm (columnPiece 0 4 outputData) := by decide +kernel

theorem column4_weights : ∀ i : Fin 5,SmallLevelTwentySixIntegerRow89ColumnFour.inputs i=weights i := by decide +kernel

theorem column4_eval (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun k => if k=4 then 1 else 0) outputData=
      eval x y z w a b c (weightValue x y z w a b c) (column inputs (List.range 5) 4) := by
  have h:=SmallLevelTwentySixIntegerRow89ColumnFour.column_certificate x y z w a b c hx hy hz hw
  rw [SmallLevelIntegerLaurentColumnOutput.eval_perm x y z w a b c _ column4_operation] at h
  have hh:=SmallLevelIntegerLaurentColumnOutput.column_output x y z w a b c inputs
    SmallLevelTwentySixIntegerRow89ColumnFour.inputs outputData 5 4 column4_output h
  rw [hh]
  simp only [SmallLevelIntegerLaurentColumnOutput.eval_column_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hb:=column4_weights ⟨i,List.mem_range.mp hi⟩
  change _=weightValue x y z w a b c i*_
  rw [hb]
  rfl

#print axioms column4_eval

theorem column5_operation : SmallLevelTwentySixIntegerRow89ColumnFive.operationData.Perm
    (column inputs (List.range 5) 5++[(-1,5,(0,0,0,0,0,0,0))]) := by decide +kernel

theorem column5_output : (SmallLevelTwentySixIntegerRow89ColumnFive.inputs 5).Perm (columnPiece 0 5 outputData) := by decide +kernel

theorem column5_weights : ∀ i : Fin 5,SmallLevelTwentySixIntegerRow89ColumnFive.inputs i=weights i := by decide +kernel

theorem column5_eval (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun k => if k=5 then 1 else 0) outputData=
      eval x y z w a b c (weightValue x y z w a b c) (column inputs (List.range 5) 5) := by
  have h:=SmallLevelTwentySixIntegerRow89ColumnFive.column_certificate x y z w a b c hx hy hz hw
  rw [SmallLevelIntegerLaurentColumnOutput.eval_perm x y z w a b c _ column5_operation] at h
  have hh:=SmallLevelIntegerLaurentColumnOutput.column_output x y z w a b c inputs
    SmallLevelTwentySixIntegerRow89ColumnFive.inputs outputData 5 5 column5_output h
  rw [hh]
  simp only [SmallLevelIntegerLaurentColumnOutput.eval_column_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hb:=column5_weights ⟨i,List.mem_range.mp hi⟩
  change _=weightValue x y z w a b c i*_
  rw [hb]
  rfl

#print axioms column5_eval

end SmallLevelTwentySixIntegerRow89Transpose
end
