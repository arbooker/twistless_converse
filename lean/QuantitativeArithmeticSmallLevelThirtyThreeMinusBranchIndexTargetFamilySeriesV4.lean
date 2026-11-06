module
public import QuantitativeArithmeticSmallLevelThirtyThreeMinusBranchIndexTargetIndexStagesBundleSeriesV4
@[expose] public noncomputable section
section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

namespace QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1
open QuantitativeArithmeticSevenLaurentRows
theorem value0_eq : value0=target := by decide +kernel
theorem certificate : substituteCompute inputs operations=target := by
  simpa only [List.drop_zero,value0_eq] using tail_0
theorem target_zero (X Y Z : ℂ)
    (h : ∀ i,eval 1 1 1 1 X Y Z (fun _ => 1) (inputs i)=0) :
    eval 1 1 1 1 X Y Z (fun _ => 1) target=0 := by
  rw [← certificate,substituteCompute_eq,eval_substitute _ _ _ _ _ _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [h]
  simp [eval]

#print axioms target_zero
end QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target1
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

namespace QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target2
open QuantitativeArithmeticSevenLaurentRows
theorem value0_eq : value0=target := by decide +kernel
theorem certificate : substituteCompute inputs operations=target := by
  simpa only [List.drop_zero,value0_eq] using tail_0
theorem target_zero (X Y Z : ℂ)
    (h : ∀ i,eval 1 1 1 1 X Y Z (fun _ => 1) (inputs i)=0) :
    eval 1 1 1 1 X Y Z (fun _ => 1) target=0 := by
  rw [← certificate,substituteCompute_eq,eval_substitute _ _ _ _ _ _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [h]
  simp [eval]

#print axioms target_zero
end QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Target2
end
end

section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

namespace QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch3Target1
open QuantitativeArithmeticSevenLaurentRows
theorem value0_eq : value0=target := by decide +kernel
theorem certificate : substituteCompute inputs operations=target := by
  simpa only [List.drop_zero,value0_eq] using tail_0
theorem target_zero (X Y Z : ℂ)
    (h : ∀ i,eval 1 1 1 1 X Y Z (fun _ => 1) (inputs i)=0) :
    eval 1 1 1 1 X Y Z (fun _ => 1) target=0 := by
  rw [← certificate,substituteCompute_eq,eval_substitute _ _ _ _ _ _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [h]
  simp [eval]

#print axioms target_zero
end QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch3Target1
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

namespace QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch3Target2
open QuantitativeArithmeticSevenLaurentRows
theorem value0_eq : value0=target := by decide +kernel
theorem certificate : substituteCompute inputs operations=target := by
  simpa only [List.drop_zero,value0_eq] using tail_0
theorem target_zero (X Y Z : ℂ)
    (h : ∀ i,eval 1 1 1 1 X Y Z (fun _ => 1) (inputs i)=0) :
    eval 1 1 1 1 X Y Z (fun _ => 1) target=0 := by
  rw [← certificate,substituteCompute_eq,eval_substitute _ _ _ _ _ _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [h]
  simp [eval]

#print axioms target_zero
end QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch3Target2
end
end
