module

public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! Consolidated chapter: QuantitativeArithmeticFiniteRowCombination. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticFiniteRowCombinationV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticFiniteRowCombination
open Matrix
 theorem kernel_of_combination {R : Type*} [Semiring R] {r n : ℕ} (A : Fin r → Fin n → R)
    (w : Fin r → R) (b v : Fin n → R)
    (hA : ∀ i, dotProduct (A i) v = 0)
    (hb : ∀ j, b j = ∑ i, w i * A i j) : dotProduct b v = 0 := by
  simp only [dotProduct, hb, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  change (∑ i, w i * dotProduct (A i) v) = 0
  simp only [hA, mul_zero, Finset.sum_const_zero]
end QuantitativeArithmeticFiniteRowCombination
end
end

/-! ## QuantitativeArithmeticFiniteRowCombinationScaledV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticFiniteRowCombination
 theorem scaled_kernel {R : Type*} [Semiring R] {r n : ℕ}
    (A : Fin r → Fin n → R) (w : Fin r → R) (C v : Fin n → R) (E : R)
    (hA : ∀ i, dotProduct (A i) v = 0)
    (hC : ∀ j, E*C j = ∑ i, w i * A i j) : E*dotProduct C v = 0 := by
  have h := kernel_of_combination A w (fun j => E*C j) v hA hC
  simpa only [dotProduct, Finset.mul_sum, mul_assoc] using h
end QuantitativeArithmeticFiniteRowCombination
end
end
