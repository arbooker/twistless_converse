module
public import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
@[expose] public section
namespace QuantitativeArithmeticMonomialCancellation
theorem cancel (D d e P : ℂ) (hd : d ≠ 0) (hD : D = e*d) :
    D*(P/d)=e*P := by
  rw [hD, mul_assoc, mul_div_cancel₀ _ hd]
end QuantitativeArithmeticMonomialCancellation
