module

public import QuantitativeMaassMajorantMovingGeometryV1
public import QuantitativeMaassAmbientGramTraceV1
public import QuantitativeMaassAmbientParityFilterV1
public import QuantitativeMaassColumnParityGramV1
public import QuantitativeArithmeticMaassScheduledBroadErrorV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter MeasureTheory ContinuousLinearMap AsymptoticSectorSigns
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The actual new/sign filter has the parity main term one half of its
ordinary regular main integral. Its spatial cutoff mass is retained. -/
theorem originalMajorant_sector_parity_trace_decay {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N) (σ : ℝ)
    (δ P D : ℝ) (hδ : 0<δ) (hP : 0≤P)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t =>
      let c := fun z => cutoffTransfer N (movingLowerEdge δ P ε t) D t
        (movingLowerEdge_pos hδ P ε t) (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))
      let F := ambientSectorNewFilter N hN e (growingLVDegree t)
      Real.exp (W*Strong.strongScale t)*
        (columnLinearTrace (quotientMeasure 0) (fun z => F (c z)) (parityProjection N σ)-
          ((QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹^2*enlargedMovingExpressionMain N (ambientSectorGramExpression N hN e) δ P D hδ K hc ε t)/2)/
        (t*ε t)) atTop (𝓝 0) := by
  let E := ambientSectorGramExpression N hN e
  let F := fun m => ambientSectorNewFilter N hN e m
  let A := fun m => (F m).adjoint.comp (F m)
  let c := fun t z => cutoffTransfer N (movingLowerEdge δ P ε t) D t
    (movingLowerEdge_pos hδ P ε t) (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))
  have hE : ExponentialExpressionGrowth E := ambientSectorGramExpression_cost N hN e
  have hA : ∀ m,QuotientRealizes N (E m) (A m) :=
    ambientSectorGramExpression_realizes N hN e
  have ho := originalMajorant_moving_regular_trace_decay basis N E A hE hA
    δ P D hδ hP K hc he ε hε hp W
  have hr := originalMajorant_moving_reflected_trace_decay basis N E A hE hA
    δ P D hδ hP K hc he ε hε hp W
  have hh := (ho.add (hr.const_mul σ)).div_const 2
  simp only [mul_zero,add_zero,zero_div] at hh
  have hm (t : ℝ) : MemLp (c t) 2 (quotientMeasure 0) :=
    originalMajorant_cutoff_memLp N hδ P D K hc he ε t
  convert hh using 1
  funext t
  change Real.exp (W*Strong.strongScale t)*
    (columnLinearTrace (quotientMeasure 0) (fun z => F (growingLVDegree t) (c t z))
      (parityProjection N σ)-((QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹^2*enlargedMovingExpressionMain N E δ P D hδ K hc ε t)/2)/(t*ε t)=_
  rw [columnLinearTrace_filtered_parity _ N _ (hm t) _ σ
    (ambientSectorNewFilter_reflection N hN e (growingLVDegree t))]
  dsimp only [A,c]
  ring

#print axioms originalMajorant_sector_parity_trace_decay
end QuantitativeMaass.Scheduled
