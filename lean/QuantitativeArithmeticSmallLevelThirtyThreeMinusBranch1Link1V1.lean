module
public import QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch1Target1V1
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
    eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch1Target1.inputs 0)=
      eval X Y Z 1 (-X) 1 1 (fun _ => 1) minor6 := by
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch1Target1.inputs,minor6,eval,monomial]
  ring

private theorem input1_identity (X Y Z : ℂ) :
    eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch1Target1.inputs 1)=
      eval X Y Z 1 (-X) 1 1 (fun _ => 1) minor12 := by
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch1Target1.inputs,minor12,eval,monomial]
  ring

private theorem input2_identity (X Y Z : ℂ) :
    eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch1Target1.inputs 2)=
      eval X Y Z 1 (-X) 1 1 (fun _ => 1) minor25 := by
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch1Target1.inputs,minor25,eval,monomial]
  ring

theorem branch1_target1 (X Y Z : ℂ)
    (h6 : eval X Y Z 1 (-X) 1 1 (fun _ => 1) minor6=0)
    (h12 : eval X Y Z 1 (-X) 1 1 (fun _ => 1) minor12=0)
    (h25 : eval X Y Z 1 (-X) 1 1 (fun _ => 1) minor25=0)
    : X^2-Y-1=0 := by
  have hi : ∀ i,eval 1 1 1 1 X Y Z (fun _ => 1) (QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch1Target1.inputs i)=0 := by
    intro i
    by_cases hi : i<3
    · interval_cases i
      · exact (input0_identity X Y Z).trans h6
      · exact (input1_identity X Y Z).trans h12
      · exact (input2_identity X Y Z).trans h25
    · have he : QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch1Target1.inputs i=[] := by
        have hn0 : i≠0 := by omega
        have hn1 : i≠1 := by omega
        have hn2 : i≠2 := by omega
        simp [QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch1Target1.inputs,hn0,hn1,hn2]
      rw [he,eval_nil]
  have ht := QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch1Target1.target_zero X Y Z hi
  convert ht using 1 <;> norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch1Target1.target,eval,monomial] <;> ring

#print axioms branch1_target1
end QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination
