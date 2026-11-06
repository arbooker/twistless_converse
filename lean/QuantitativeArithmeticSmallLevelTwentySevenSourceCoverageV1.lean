module
public import QuantitativeArithmeticSmallLevelTwentySevenHeckeSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenRamanujanSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenMatrixSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenEntireSourceTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenSourceCoverage

def entireIndices : List ℕ := (List.finRange 8).map QuantitativeArithmeticSmallLevelTwentySevenEntireSource.source

abbrev Covered (i : ℕ) : Prop := i∈QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.indices ∨ i∈QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.specs.map QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec.source ∨
  i∈QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.specs.map QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec.source ∨ i∈entireIndices

private theorem coverage_check : (List.range 550).all (fun i => decide (Covered i))=true := by
  decide +kernel

/-- Every row of the actual 550-row reconstruction matrix has an original
analytic source; no selected row is left as an assumed relation. -/
theorem coverage (i : Fin 550) : Covered i.val := by
  exact of_decide_eq_true (List.all_eq_true.mp coverage_check i.val (List.mem_range.mpr i.isLt))
#print axioms coverage
end QuantitativeArithmeticSmallLevelTwentySevenSourceCoverage
