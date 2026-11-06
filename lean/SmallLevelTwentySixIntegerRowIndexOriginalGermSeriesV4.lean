module
public import SmallLevelIntegerLaurentGermTheoryV4
public import SmallLevelTwentySixGermDAGSignedPrimitiveGermsV1
public import SmallLevelTwentySixIntegerRowIndexTransposeGermSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false

namespace SmallLevelTwentySixIntegerRow87Transpose
open SmallLevelTwentySixGermSources SmallLevelPrimeRates QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGrid (phase badParameter)

/-- The polynomial row87 certificate acts on the actual original
continued functions, with no nonvanishing pivot assumption. -/
theorem original_output_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v) :
    HasAnalyticGerm (fun z => QuantitativeArithmeticIntegerSevenLaurentRows.eval
      (u*parameter 2 m z) ((parameter 3 m z)^2)
      (v*parameter 13 m z) ((parameter 5 m z)^2)
      (badParameter f 3*parameter 3 m z) (badParameter f 5*parameter 5 m z)
      1 (replayVector m S.G z) outputData) x := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX : ∀ z,u*parameter 2 m z≠0 := fun z => mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) z)
  have hY : ∀ z,(parameter 3 m z)^2≠0 := fun z => pow_ne_zero 2 (parameter_ne_zero 3 m (by decide) z)
  have hZ : ∀ z,v*parameter 13 m z≠0 := fun z => mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) z)
  have hW : ∀ z,(parameter 5 m z)^2≠0 := fun z => pow_ne_zero 2 (parameter_ne_zero 5 m (by decide) z)
  apply output_germ (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
    (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
    (fun z => badParameter f 3*parameter 3 m z)
    (fun z => badParameter f 5*parameter 5 m z) (fun _ => 1) x (replayVector m S.G)
  · exact analyticAt_const.mul (parameter_analytic 2 m (by decide) x)
  · exact (parameter_analytic 3 m (by decide) x).pow 2
  · exact analyticAt_const.mul (parameter_analytic 13 m (by decide) x)
  · exact (parameter_analytic 5 m (by decide) x).pow 2
  · exact analyticAt_const.mul (parameter_analytic 3 m (by decide) x)
  · exact analyticAt_const.mul (parameter_analytic 5 m (by decide) x)
  · exact analyticAt_const
  · exact hX
  · exact hY
  · exact hZ
  · exact hW
  · intro i hi
    have hi5 : i<5 := List.mem_range.mp hi
    interval_cases i
    · apply SmallLevelIntegerLaurentGerm.scaled_source_germ
        (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
        (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
        (fun z => badParameter f 3*parameter 3 m z)
        (fun z => badParameter f 5*parameter 5 m z) (fun _ => 1) x (replayVector m S.G)
        input0 SmallLevelTwentySixGermPrimitiveSparseMMM.Row87.primitiveData _
        hX hY hZ hW input0_binding
      exact SmallLevelTwentySixGermDAG.signed_original_primitive_germs
        S x u v hu hv hshift hx hx1 hη hs2 hs13 87
    · apply SmallLevelIntegerLaurentGerm.scaled_source_germ
        (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
        (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
        (fun z => badParameter f 3*parameter 3 m z)
        (fun z => badParameter f 5*parameter 5 m z) (fun _ => 1) x (replayVector m S.G)
        input1 SmallLevelTwentySixGermPrimitiveSparseMMM.Row10.primitiveData _
        hX hY hZ hW input1_binding
      exact SmallLevelTwentySixGermDAG.signed_original_primitive_germs
        S x u v hu hv hshift hx hx1 hη hs2 hs13 10
    · apply SmallLevelIntegerLaurentGerm.scaled_source_germ
        (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
        (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
        (fun z => badParameter f 3*parameter 3 m z)
        (fun z => badParameter f 5*parameter 5 m z) (fun _ => 1) x (replayVector m S.G)
        input2 SmallLevelTwentySixGermPrimitiveSparseMMM.Row32.primitiveData _
        hX hY hZ hW input2_binding
      exact SmallLevelTwentySixGermDAG.signed_original_primitive_germs
        S x u v hu hv hshift hx hx1 hη hs2 hs13 32
    · apply SmallLevelIntegerLaurentGerm.scaled_source_germ
        (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
        (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
        (fun z => badParameter f 3*parameter 3 m z)
        (fun z => badParameter f 5*parameter 5 m z) (fun _ => 1) x (replayVector m S.G)
        input3 SmallLevelTwentySixGermPrimitiveSparseMMM.Row62.primitiveData _
        hX hY hZ hW input3_binding
      exact SmallLevelTwentySixGermDAG.signed_original_primitive_germs
        S x u v hu hv hshift hx hx1 hη hs2 hs13 62
    · apply SmallLevelIntegerLaurentGerm.scaled_source_germ
        (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
        (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
        (fun z => badParameter f 3*parameter 3 m z)
        (fun z => badParameter f 5*parameter 5 m z) (fun _ => 1) x (replayVector m S.G)
        input4 SmallLevelTwentySixGermPrimitiveSparseMMM.Row71.primitiveData _
        hX hY hZ hW input4_binding
      exact SmallLevelTwentySixGermDAG.signed_original_primitive_germs
        S x u v hu hv hshift hx hx1 hη hs2 hs13 71

#print axioms original_output_germ
end SmallLevelTwentySixIntegerRow87Transpose
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false

namespace SmallLevelTwentySixIntegerRow89Transpose
open SmallLevelTwentySixGermSources SmallLevelPrimeRates QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGrid (phase badParameter)

/-- The polynomial row89 certificate acts on the actual original
continued functions, with no nonvanishing pivot assumption. -/
theorem original_output_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v) :
    HasAnalyticGerm (fun z => QuantitativeArithmeticIntegerSevenLaurentRows.eval
      (u*parameter 2 m z) ((parameter 3 m z)^2)
      (v*parameter 13 m z) ((parameter 5 m z)^2)
      (badParameter f 3*parameter 3 m z) (badParameter f 5*parameter 5 m z)
      1 (replayVector m S.G z) outputData) x := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX : ∀ z,u*parameter 2 m z≠0 := fun z => mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) z)
  have hY : ∀ z,(parameter 3 m z)^2≠0 := fun z => pow_ne_zero 2 (parameter_ne_zero 3 m (by decide) z)
  have hZ : ∀ z,v*parameter 13 m z≠0 := fun z => mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) z)
  have hW : ∀ z,(parameter 5 m z)^2≠0 := fun z => pow_ne_zero 2 (parameter_ne_zero 5 m (by decide) z)
  apply output_germ (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
    (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
    (fun z => badParameter f 3*parameter 3 m z)
    (fun z => badParameter f 5*parameter 5 m z) (fun _ => 1) x (replayVector m S.G)
  · exact analyticAt_const.mul (parameter_analytic 2 m (by decide) x)
  · exact (parameter_analytic 3 m (by decide) x).pow 2
  · exact analyticAt_const.mul (parameter_analytic 13 m (by decide) x)
  · exact (parameter_analytic 5 m (by decide) x).pow 2
  · exact analyticAt_const.mul (parameter_analytic 3 m (by decide) x)
  · exact analyticAt_const.mul (parameter_analytic 5 m (by decide) x)
  · exact analyticAt_const
  · exact hX
  · exact hY
  · exact hZ
  · exact hW
  · intro i hi
    have hi5 : i<5 := List.mem_range.mp hi
    interval_cases i
    · apply SmallLevelIntegerLaurentGerm.scaled_source_germ
        (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
        (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
        (fun z => badParameter f 3*parameter 3 m z)
        (fun z => badParameter f 5*parameter 5 m z) (fun _ => 1) x (replayVector m S.G)
        input0 SmallLevelTwentySixGermPrimitiveSparseMMM.Row89.primitiveData _
        hX hY hZ hW input0_binding
      exact SmallLevelTwentySixGermDAG.signed_original_primitive_germs
        S x u v hu hv hshift hx hx1 hη hs2 hs13 89
    · apply SmallLevelIntegerLaurentGerm.scaled_source_germ
        (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
        (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
        (fun z => badParameter f 3*parameter 3 m z)
        (fun z => badParameter f 5*parameter 5 m z) (fun _ => 1) x (replayVector m S.G)
        input1 SmallLevelTwentySixGermPrimitiveSparseMMM.Row10.primitiveData _
        hX hY hZ hW input1_binding
      exact SmallLevelTwentySixGermDAG.signed_original_primitive_germs
        S x u v hu hv hshift hx hx1 hη hs2 hs13 10
    · apply SmallLevelIntegerLaurentGerm.scaled_source_germ
        (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
        (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
        (fun z => badParameter f 3*parameter 3 m z)
        (fun z => badParameter f 5*parameter 5 m z) (fun _ => 1) x (replayVector m S.G)
        input2 SmallLevelTwentySixGermPrimitiveSparseMMM.Row32.primitiveData _
        hX hY hZ hW input2_binding
      exact SmallLevelTwentySixGermDAG.signed_original_primitive_germs
        S x u v hu hv hshift hx hx1 hη hs2 hs13 32
    · apply SmallLevelIntegerLaurentGerm.scaled_source_germ
        (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
        (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
        (fun z => badParameter f 3*parameter 3 m z)
        (fun z => badParameter f 5*parameter 5 m z) (fun _ => 1) x (replayVector m S.G)
        input3 SmallLevelTwentySixGermPrimitiveSparseMMM.Row62.primitiveData _
        hX hY hZ hW input3_binding
      exact SmallLevelTwentySixGermDAG.signed_original_primitive_germs
        S x u v hu hv hshift hx hx1 hη hs2 hs13 62
    · apply SmallLevelIntegerLaurentGerm.scaled_source_germ
        (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
        (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
        (fun z => badParameter f 3*parameter 3 m z)
        (fun z => badParameter f 5*parameter 5 m z) (fun _ => 1) x (replayVector m S.G)
        input4 SmallLevelTwentySixGermPrimitiveSparseMMM.Row71.primitiveData _
        hX hY hZ hW input4_binding
      exact SmallLevelTwentySixGermDAG.signed_original_primitive_germs
        S x u v hu hv hshift hx hx1 hη hs2 hs13 71

#print axioms original_output_germ
end SmallLevelTwentySixIntegerRow89Transpose
end
