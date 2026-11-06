module
public import QuantitativeArithmeticSmallLevelThirtyThreePlusBranchIndexTargetFamilySeriesV4
public import QuantitativeArithmeticSmallLevelThirtyThreePlusEliminationTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
open QuantitativeArithmeticSevenLaurentRows

private theorem input0_identity (X Y Z : ℂ) :
    eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Target2.inputs 0)=
      eval X (3/2) Z 1 Y 1 1 (fun _ => 1) minor3 := by
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Target2.inputs,minor3,eval,monomial]
  ring

private theorem input1_identity (X Y Z : ℂ) :
    eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Target2.inputs 1)=
      eval X (3/2) Z 1 Y 1 1 (fun _ => 1) minor6 := by
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Target2.inputs,minor6,eval,monomial]
  ring

private theorem input2_identity (X Y Z : ℂ) :
    eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Target2.inputs 2)=
      eval X (3/2) Z 1 Y 1 1 (fun _ => 1) minor13 := by
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Target2.inputs,minor13,eval,monomial]
  ring

private theorem input3_identity (X Y Z : ℂ) :
    eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Target2.inputs 3)=
      eval X (3/2) Z 1 Y 1 1 (fun _ => 1) minor25 := by
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Target2.inputs,minor25,eval,monomial]
  ring

theorem branch3_target2 (X Y Z : ℂ)
    (h3 : eval X (3/2) Z 1 Y 1 1 (fun _ => 1) minor3=0)
    (h6 : eval X (3/2) Z 1 Y 1 1 (fun _ => 1) minor6=0)
    (h13 : eval X (3/2) Z 1 Y 1 1 (fun _ => 1) minor13=0)
    (h25 : eval X (3/2) Z 1 Y 1 1 (fun _ => 1) minor25=0)
    : X^2-5/2=0 := by
  have hi : ∀ i,eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Target2.inputs i)=0 := by
    intro i
    by_cases hi : i<4
    · interval_cases i
      · exact (input0_identity X Y Z).trans h3
      · exact (input1_identity X Y Z).trans h6
      · exact (input2_identity X Y Z).trans h13
      · exact (input3_identity X Y Z).trans h25
    · have he : QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Target2.inputs i=[] := by
        have hn0 : i≠0 := by omega
        have hn1 : i≠1 := by omega
        have hn2 : i≠2 := by omega
        have hn3 : i≠3 := by omega
        simp [QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Target2.inputs,hn0,hn1,hn2,hn3]
      rw [he,eval_nil]
  have ht := QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Target2.target_zero X Y Z hi
  convert ht using 1 <;> norm_num [QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Target2.target,eval,monomial] <;> ring

#print axioms branch3_target2
end QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
