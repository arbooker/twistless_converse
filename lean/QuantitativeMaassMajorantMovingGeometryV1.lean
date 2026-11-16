module

public import QuantitativeMaassEnlargedMovingRegularTraceV1
public import QuantitativeMaassCrossEnlargedWindowV1
public import QuantitativeMaassCrossRegularIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson AsymptoticMassTransport QuantitativeHolomorphic AsymptoticRegularTrace
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

attribute [local instance] Classical.propDecidable

/-- The literal normalized majorant inherits the enlarged packet comparison. -/
theorem originalMajorant_moving_reflected_trace_decay {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (N : ℕ) (E : ℕ → Expression)
    (A : ℕ → AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hE : ExponentialExpressionGrowth E) (hA : ∀ m, QuotientRealizes N (E m) (A m))
    (δ P D : ℝ) (hδ : 0 < δ) (hP : 0 ≤ P)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      columnLinearTrace (quotientMeasure 0)
        (fun z => cutoffTransfer N (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t)
          (cylinderAutomorphic (originalMajorantColumn K hc he ε t z)))
        ((reflectionIsometry N).toContinuousLinearMap.comp (A (growingLVDegree t)))/(t*ε t))
      atTop (𝓝 0) := by
  have hlim := enlarged_moving_expression_reflected_trace_decay basis N E A hE hA δ P D hδ hP K hc he ε hε hp W
  have hh := (originalMajorant_normalization_sq_limit K ε (hε.mono (fun _ h => h.1)) hp).mul hlim
  rw [mul_zero] at hh
  convert hh using 1
  funext t
  rw [originalMajorant_transferred_trace_eq]
  ring

/-- The literal normalized majorant inherits the enlarged packet comparison. -/
theorem originalMajorant_moving_regular_trace_decay {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (N : ℕ) (E : ℕ → Expression)
    (A : ℕ → AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hE : ExponentialExpressionGrowth E) (hA : ∀ m, QuotientRealizes N (E m) (A m))
    (δ P D : ℝ) (hδ : 0 < δ) (hP : 0 ≤ P)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (columnLinearTrace (quotientMeasure 0)
        (fun z => cutoffTransfer N (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t)
          (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))) (A (growingLVDegree t))-
        (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹^2*
          enlargedMovingExpressionMain N E δ P D hδ K hc ε t)/(t*ε t))
      atTop (𝓝 0) := by
  have hlim := enlarged_moving_expression_regular_trace_decay basis N E A hE hA δ P D hδ hP K hc he ε hε hp W
  have hh := (originalMajorant_normalization_sq_limit K ε (hε.mono (fun _ h => h.1)) hp).mul hlim
  rw [mul_zero] at hh
  convert hh using 1
  funext t
  rw [originalMajorant_transferred_trace_eq]
  ring

#print axioms originalMajorant_moving_reflected_trace_decay
#print axioms originalMajorant_moving_regular_trace_decay
end QuantitativeMaass.Scheduled
