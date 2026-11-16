module

public import QuantitativeMaassAmbientAdjointExpressionV1
public import QuantitativeMaassAmbientExpressionCostV1
public import QuantitativeMaassColumnLinearTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open AsymptoticFiniteBranch AsymptoticSectorSigns QuantitativeHolomorphic
open MeasureTheory ContinuousLinearMap QuantitativeNewGap
namespace QuantitativeMaass

theorem ambientSectorAdjointExpression_growth (N : ℕ) [NeZero N]
    (hN : 0<N) (e : Sector N) :
    ExponentialExpressionGrowth (ambientSectorAdjointExpression N hN e) :=
  (ExponentialExpressionGrowth.constant
    (orderedProductExpression (ambientSignFactorExpression N hN e)
      (Finset.univ : Finset (SectorSignIndex N)).toList.reverse)).compose
    (ExponentialExpressionGrowth.ordered_product _ (ambientLocalNewExpression_growth N hN)
      (Finset.univ : Finset ↥N.primeFactors).toList.reverse)

/-- Both the coefficients and matrix heights of the actual Gram expression
grow at most exponentially in its polynomial degree. -/
theorem ambientSectorGramExpression_cost (N : ℕ) [NeZero N]
    (hN : 0<N) (e : Sector N) :
    ∃ C : ℝ,0≤C ∧ ∀ m : ℕ,
      expressionBound (ambientSectorGramExpression N hN e m)≤Real.exp (C*((m:ℝ)+1)) ∧
      ExpressionMatrixBound (ambientSectorGramExpression N hN e m) (Real.exp (C*((m:ℝ)+1))) :=
  (ambientSectorAdjointExpression_growth N hN e).compose (ambientSectorNewExpression_cost N hN e)

/-- Move a bounded column filter into its Gram operator. This is a pointwise
identity, so it does not require a global trace-class assumption. -/
theorem columnLinearTrace_gram {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure α) (c : α→H) (F : H→L[ℂ]H) :
    columnLinearTrace μ (fun z => F (c z)) 1 =
      columnLinearTrace μ c (F.adjoint.comp F) := by
  unfold columnLinearTrace
  apply integral_congr_ae
  filter_upwards with z
  change (inner ℂ (F (c z)) (F (c z))).re =
    (inner ℂ (F.adjoint (F (c z))) (c z)).re
  rw [F.adjoint_inner_left]

theorem ambientSectorNewFilter_column_trace {α : Type*} [MeasurableSpace α]
    (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N) (m : ℕ)
    (μ : Measure α) (c : α→AutomorphicSpace N) :
    columnLinearTrace μ (fun z => ambientSectorNewFilter N hN e m (c z)) 1 =
      columnLinearTrace μ c
        ((ambientSectorNewFilter N hN e m).adjoint.comp (ambientSectorNewFilter N hN e m)) :=
  columnLinearTrace_gram μ c _

#print axioms ambientSectorGramExpression_cost
#print axioms columnLinearTrace_gram
#print axioms ambientSectorNewFilter_column_trace

end QuantitativeMaass
