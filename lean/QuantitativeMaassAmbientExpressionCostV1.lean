module

public import QuantitativeMaassExpressionGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open AsymptoticFiniteBranch QuantitativeHolomorphic AsymptoticSectorSigns
namespace QuantitativeMaass

theorem ambientLocalNewExpression_growth (N : ℕ) [NeZero N] (hN : 0<N)
    (p : ↥N.primeFactors) :
    ExponentialExpressionGrowth (fun m => ambientLocalNewExpression N hN m p) := by
  classical
  by_cases hp : p.val∣N/p.val
  · simp only [ambientLocalNewExpression,ite_eq_left hp]
    exact ExponentialExpressionGrowth.constant _
  · simp only [ambientLocalNewExpression,ite_eq_right hp,ambientSimpleNewExpression]
    exact ExponentialExpressionGrowth.power _

theorem ambientTotalNewExpression_growth (N : ℕ) [NeZero N] (hN : 0<N) :
    ExponentialExpressionGrowth (ambientTotalNewExpression N hN) :=
  ExponentialExpressionGrowth.ordered_product _ (ambientLocalNewExpression_growth N hN) _

/-- Explicit exponential coefficient and integer-height bounds for the
constructed actual ambient filter. The constants precede every degree;
no auxiliary projection or spectral-gap premise appears. -/
theorem ambientSectorNewExpression_cost (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N) :
    ∃ C : ℝ,0≤C ∧ ∀ m : ℕ,
      expressionBound (ambientSectorNewExpression N hN e m)≤Real.exp (C*((m:ℝ)+1)) ∧
      ExpressionMatrixBound (ambientSectorNewExpression N hN e m) (Real.exp (C*((m:ℝ)+1))) :=
  (ambientTotalNewExpression_growth N hN).compose
    (ExponentialExpressionGrowth.constant (ambientSignProductExpression N hN e))

#print axioms ambientLocalNewExpression_growth
#print axioms ambientTotalNewExpression_growth
#print axioms ambientSectorNewExpression_cost
end QuantitativeMaass
