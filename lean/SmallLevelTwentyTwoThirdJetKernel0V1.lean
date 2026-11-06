module
public import QuantitativeArithmeticCompact22ArrayKernelTheoryV4
public import QuantitativeArithmeticRationalRowsTheoryV4
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoThirdJet
open QuantitativeArithmeticRationalRows
open QuantitativeArithmeticCompact22ArrayKernel

/-- The original kernel theorem, with the exact rational certificate verified
inside Lean instead of repeating one linear-combination proof per coordinate. -/
theorem kernel0 (w : Fin 264 → ℂ) (hw : ∀ i, rows0 w i=0) : w=0 :=
  kernel_of_certificates inputs certificates rows0 inputs_eq checked
    (fun i t ht => of_decide_eq_true (List.all_eq_true.mp (support i) t ht)) w hw

#print axioms kernel0
end SmallLevelTwentyTwoThirdJet
