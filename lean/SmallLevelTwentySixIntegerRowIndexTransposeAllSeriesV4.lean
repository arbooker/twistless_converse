module
public import SmallLevelTwentySixIntegerRowIndexTransposeColumnBundleSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

namespace SmallLevelTwentySixIntegerRow87Transpose
open QuantitativeArithmeticIntegerSevenLaurentRows

theorem output_eval (x y z w a b c : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c v outputData=
      ((List.range 5).map fun i => weightValue x y z w a b c i*
        eval x y z w a b c v (inputs i)).sum := by
  apply SmallLevelIntegerLaurentColumnOutput.output_of_columns x y z w a b c v
    (weightValue x y z w a b c) inputs outputData (List.range 5) (Finset.range 6)
  · intro i hi
    exact input_support ⟨i,List.mem_range.mp hi⟩
  · exact output_support
  · intro j hj
    have hj' : j<6:=Finset.mem_range.mp hj
    interval_cases j
    · exact column0_eval x y z w a b c hx hy hz hw
    · exact column1_eval x y z w a b c hx hy hz hw
    · exact column2_eval x y z w a b c hx hy hz hw
    · exact column3_eval x y z w a b c hx hy hz hw
    · exact column4_eval x y z w a b c hx hy hz hw
    · exact column5_eval x y z w a b c hx hy hz hw

#print axioms output_eval

end SmallLevelTwentySixIntegerRow87Transpose
end

section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

namespace SmallLevelTwentySixIntegerRow89Transpose
open QuantitativeArithmeticIntegerSevenLaurentRows

theorem output_eval (x y z w a b c : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c v outputData=
      ((List.range 5).map fun i => weightValue x y z w a b c i*
        eval x y z w a b c v (inputs i)).sum := by
  apply SmallLevelIntegerLaurentColumnOutput.output_of_columns x y z w a b c v
    (weightValue x y z w a b c) inputs outputData (List.range 5) (Finset.range 6)
  · intro i hi
    exact input_support ⟨i,List.mem_range.mp hi⟩
  · exact output_support
  · intro j hj
    have hj' : j<6:=Finset.mem_range.mp hj
    interval_cases j
    · exact column0_eval x y z w a b c hx hy hz hw
    · exact column1_eval x y z w a b c hx hy hz hw
    · exact column2_eval x y z w a b c hx hy hz hw
    · exact column3_eval x y z w a b c hx hy hz hw
    · exact column4_eval x y z w a b c hx hy hz hw
    · exact column5_eval x y z w a b c hx hy hz hw

#print axioms output_eval

end SmallLevelTwentySixIntegerRow89Transpose
end
