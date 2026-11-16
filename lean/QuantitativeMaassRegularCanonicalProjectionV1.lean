module

public import QuantitativeMaassRegularMetricTraceV1
public import AsymptoticIncidenceCountReductionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip
open AsymptoticNestedQuotients AsymptoticSectorSigns QuantitativeNewGap
open AsymptoticRegularTrace ContinuousLinearMap
open scoped lp ENNReal
namespace QuantitativeMaass.CountingMetric

variable {ι : Type*} [Fintype ι] [Nonempty ι]
    (N : ℕ) (g : ι→quotientNormalizerGroup N)
    {δ Y : ℝ} (hδ : 0<δ) (hY : 0<Y) {ν : ℕ} (hν : 1≤ν)
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • ((g i).val • z)).im)
    (hN : GridAdmissibleGap.Admissible N)
    (hg : ∀ i,(g i).val∈admissibleNormalizerGroup N hN.1) (e : Sector N)

def regularCanonicalProjection (z : ℍ) :
    ℓ²(AsymptoticRationalGroup.Group,ℂ)→L[ℂ]ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  metricCompression N g hδ hY hν hcover (countingSectorSpace N hN.1 e).starProjection z

include hg in
theorem regularCanonicalProjection_cogram (z : ℍ) :
    regularCanonicalProjection N g hδ hY hν hcover hN e z=
      (regularMetricSectorIsometry N g hδ hY hν hcover hN hg e z).toContinuousLinearMap.comp
        (regularMetricSectorIsometry N g hδ hY hν hcover hN hg e z).toContinuousLinearMap.adjoint := by
  let I := (AsymptoticCongruenceQuotient.induction N hδ hν z).toContinuousLinearMap
  let D := regularMetricDiagonal N g hδ hY hν hcover z
  let K := countingSectorSpace N hN.1 e
  let S := K.subtypeL
  have hS : S.comp S.adjoint=K.starProjection := by
    rw [Submodule.adjoint_subtypeL]
    rfl
  change (I.comp ((D.comp K.starProjection).comp D.adjoint)).comp I.adjoint=
    (I.comp (D.comp S)).comp (I.comp (D.comp S)).adjoint
  rw [adjoint_comp,adjoint_comp]
  simp only [comp_assoc]
  simpa only [comp_assoc] using
    (congrArg (fun T => I.comp (D.comp (T.comp (D.adjoint.comp I.adjoint)))) hS).symm

include hg in
theorem regularCanonicalProjection_isProjection (z : ℍ) :
    IsStarProjection (regularCanonicalProjection N g hδ hY hν hcover hN e z) := by
  rw [regularCanonicalProjection_cogram N g hδ hY hν hcover hN hg e z,
    AsymptoticIsometryRange.cogram]
  exact isStarProjection_starProjection

/-- The literal canonical regular metric projection has the original
incidence trace exactly, with every metric constant absent. -/
theorem regularCanonicalProjection_trace :
    trace volume (regularCanonicalProjection N g hδ hY hν hcover hN e)=
      trace volume (fun z => (AsymptoticQuotientIncidence.space N hN.1 hδ hν e z).starProjection) := by
  let K := countingSectorSpace N hN.1 e
  have hP : K.starProjection.adjoint.comp K.starProjection=K.starProjection := by
    rw [(isSelfAdjoint_starProjection K).adjoint_eq]
    exact K.isIdempotentElem_starProjection.eq
  have hp : 0≤(matrix K.starProjection (classOf (gamma N) 1) (classOf (gamma N) 1)).re := by
    rw [←hP,matrix_gram]
    positivity
  have hh := metricCompression_trace N g hδ hY hν hcover hN.1 K.starProjection hp
  change trace volume (metricCompression N g hδ hY hν hcover K.starProjection)=_
  rw [hh]
  apply congrArg (trace volume)
  funext z
  exact (QuantitativeEulerEndpointPrepared.incidence_projection_compression N hN.1 e hδ hν z).symm

theorem regularCanonicalProjection_trace_finite :
    trace volume (regularCanonicalProjection N g hδ hY hν hcover hN e)<∞ := by
  rw [regularCanonicalProjection_trace]
  exact AsymptoticQuotientIncidence.space_trace_finite N hN.1 hδ hν e

#print axioms regularCanonicalProjection_cogram
#print axioms regularCanonicalProjection_isProjection
#print axioms regularCanonicalProjection_trace
#print axioms regularCanonicalProjection_trace_finite
end QuantitativeMaass.CountingMetric
