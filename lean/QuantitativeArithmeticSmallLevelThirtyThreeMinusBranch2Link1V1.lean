module
public import QuantitativeArithmeticSmallLevelThirtyThreeMinusBranchIndexTargetFamilySeriesV4
public import QuantitativeArithmeticSmallLevelThirtyThreeMinusEliminationTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination
open QuantitativeArithmeticSevenLaurentRows

private theorem input0_identity (X Y Z : ℂ) :
    eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1.inputs 0)=
      eval X Y Z 1 (-X-1) 1 1 (fun _ => 1) minor3 := by
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1.inputs,minor3,eval,monomial]
  ring

private theorem input1_identity (X Y Z : ℂ) :
    eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1.inputs 1)=
      eval X Y Z 1 (-X-1) 1 1 (fun _ => 1) minor12 := by
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1.inputs,minor12,eval,monomial]
  ring

private theorem input2_identity (X Y Z : ℂ) :
    eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1.inputs 2)=
      eval X Y Z 1 (-X-1) 1 1 (fun _ => 1) minor16 := by
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1.inputs,minor16,eval,monomial]
  ring

private theorem input3_identity (X Y Z : ℂ) :
    eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1.inputs 3)=
      eval X Y Z 1 (-X-1) 1 1 (fun _ => 1) minor25 := by
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1.inputs,minor25,eval,monomial]
  ring

theorem branch2_target1 (X Y Z : ℂ)
    (h3 : eval X Y Z 1 (-X-1) 1 1 (fun _ => 1) minor3=0)
    (h12 : eval X Y Z 1 (-X-1) 1 1 (fun _ => 1) minor12=0)
    (h16 : eval X Y Z 1 (-X-1) 1 1 (fun _ => 1) minor16=0)
    (h25 : eval X Y Z 1 (-X-1) 1 1 (fun _ => 1) minor25=0)
    : (-Y+3)*(704*(-Y)^7+8128*(-Y)^6+3072*(-Y)^5+19152*(-Y)^4-14256*(-Y)^3+35640*(-Y)^2-36693*(-Y)+16767)=0 := by
  have hi : ∀ i,eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1.inputs i)=0 := by
    intro i
    by_cases hi : i<4
    · interval_cases i
      · exact (input0_identity X Y Z).trans h3
      · exact (input1_identity X Y Z).trans h12
      · exact (input2_identity X Y Z).trans h16
      · exact (input3_identity X Y Z).trans h25
    · have he : QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1.inputs i=[] := by
        have hn0 : i≠0 := by omega
        have hn1 : i≠1 := by omega
        have hn2 : i≠2 := by omega
        have hn3 : i≠3 := by omega
        simp [QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1.inputs,hn0,hn1,hn2,hn3]
      rw [he,eval_nil]
  have ht := QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1.target_zero X Y Z hi
  convert ht using 1 <;> norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1.target,eval,monomial] <;> ring

#print axioms branch2_target1
end QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination
