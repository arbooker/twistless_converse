module

public import QuantitativeMaassCanonicalMetricCancellationV1
public import QuantitativeMaassJointMetricPhysicalV1
public import QuantitativeMaassColumnLinearTraceV1

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap MeasureTheory AsymptoticClassicalPetersson

namespace QuantitativeMaass.AdmissibleScalarCover

local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) :
    NormedAddCommGroup (completedNewSignSpace N hN χ) := inferInstance
local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) :
    InnerProductSpace ℂ (completedNewSignSpace N hN χ) := inferInstance

variable {N : ℕ} [NeZero N] {hN : GridAdmissibleGap.Admissible N}
    (cover : AdmissibleScalarCover N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1)

/-- The physical canonical isometry is the metric change applied to the
original weighted new/sign embedding. -/
theorem physicalNewSignIsometry_eq_metric_embedding :
    (cover.physicalNewSignIsometry hδ hν χ hχ).toContinuousLinearMap =
      (cover.metric hδ hν).change.toContinuousLinearMap.comp
        (completedNewSignWeightedEmbedding N hN.1 hδ hν χ) := by
  ext x
  rfl

/-- Both inverse-metric factors cancel in the actual canonical term, even
after an arbitrary bounded localization or inverse-cap operator. -/
theorem physicalNewSignProjection_pullback
    (K : Lp ℂ 2 (quotientMeasure 0) →L[ℂ] Lp ℂ 2 (quotientMeasure 0)) :
    let D := (cover.metric hδ hν).change.symm.toContinuousLinearMap
    let W := completedNewSignWeightedEmbedding N hN.1 hδ hν χ
    (K.comp D).comp ((cover.physicalNewSignProjection hδ hν χ hχ).comp
      (K.comp D).adjoint) = (K.comp W).comp (K.comp W).adjoint := by
  intro D W
  rw [physicalNewSignProjection, cover.physicalNewSignIsometry_eq_metric_embedding]
  exact metric_cogram_cancel (cover.metric hδ hν).change W K

/-- Exact localized canonical column energy in the original new/sign
space. The fixed scalar metric disappears, with coefficient one. -/
theorem physicalNewSignProjection_column_energy {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α → Lp ℂ 2 (quotientMeasure 0))
    (K : Lp ℂ 2 (quotientMeasure 0) →L[ℂ] Lp ℂ 2 (quotientMeasure 0)) :
    let D := (cover.metric hδ hν).change.symm.toContinuousLinearMap
    let W := completedNewSignWeightedEmbedding N hN.1 hδ hν χ
    columnLinearTrace μ c ((K.comp D).comp
      ((cover.physicalNewSignProjection hδ hν χ hχ).comp (K.comp D).adjoint)) =
      ∫ x, ‖W.adjoint (K.adjoint (c x))‖ ^ 2 ∂μ := by
  intro D W
  unfold columnLinearTrace
  rw [physicalNewSignProjection, cover.physicalNewSignIsometry_eq_metric_embedding]
  exact metric_cogram_column_integral μ c (cover.metric hδ hν).change W K

#print axioms physicalNewSignIsometry_eq_metric_embedding
#print axioms physicalNewSignProjection_pullback
#print axioms physicalNewSignProjection_column_energy

end QuantitativeMaass.AdmissibleScalarCover
