module

public import QuantitativeMaassExpressionGrowthBaseV1
public import QuantitativeMaassAmbientSectorExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticFiniteBranch QuantitativeHolomorphic
namespace QuantitativeMaass

theorem ExponentialExpressionGrowth.ordered_product {ι : Type*} (E : ι→ℕ→Expression)
    (hE : ∀ i,ExponentialExpressionGrowth (E i)) (L : List ι) :
    ExponentialExpressionGrowth (fun m => orderedProductExpression (fun i => E i m) L) := by
  induction L with
  | nil => exact ExponentialExpressionGrowth.constant [AsymptoticFiniteBranch.identity]
  | cons i L ih => exact (hE i).compose ih

#print axioms ExponentialExpressionGrowth.ordered_product
end QuantitativeMaass
