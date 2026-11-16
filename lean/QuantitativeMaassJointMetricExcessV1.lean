module

public import QuantitativeMaassJointMetricPhysicalV1
public import QuantitativeMaassMetricColumnExcessV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open ContinuousLinearMap MeasureTheory AsymptoticClassicalPetersson AsymptoticSectorSigns
namespace QuantitativeMaass.AdmissibleScalarCover

local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) : NormedAddCommGroup (completedNewSignSpace N hN χ) := inferInstance
local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) : InnerProductSpace ℂ (completedNewSignSpace N hN χ) := inferInstance

/-- The precise canonical-subtracted operator in the original count is positive. -/
theorem physical_source_excess_positive {N Q : ℕ} [NeZero N]
    {hN : GridAdmissibleGap.Admissible N} (cover : AdmissibleScalarCover N hN)
    {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (e : Sector N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let M := cover.metric P'.epsilon_pos (show 1≤P'.s+3 by omega)
    let D := M.change.symm.toContinuousLinearMap
    let Qsrc := (RawCommonReconstruction.metricCylinderSource A P e M.change).starProjection
    let Qcan := cover.physicalNewSignProjection P'.epsilon_pos (show 1≤P'.s+3 by omega)
      (sectorCharacter N hN.1 e) (sectorCharacter_norm N hN.1 e)
    (D*Qsrc*D.adjoint-D*Qcan*D.adjoint).IsPositive := by
  intro P' M D Qsrc Qcan
  let J := cover.physicalNewSignIsometry P'.epsilon_pos (show 1≤P'.s+3 by omega)
    (sectorCharacter N hN.1 e) (sectorCharacter_norm N hN.1 e)
  let W := RawCommonReconstruction.metricCylinderSource A P e M.change
  let : CompleteSpace J.toContinuousLinearMap.range :=
    J.isometry.isClosedEmbedding.isClosed_range.completeSpace_coe
  have hJW : J.toContinuousLinearMap.range≤W := by
    rintro x ⟨y,rfl⟩
    exact cover.physicalNewSignIsometry_source A P e _ (sectorCharacter_norm N hN.1 e)
      (sectorCharacter_coherent N hN.1 e).1 (sectorCharacter_coherent N hN.1 e).2 y
  have hQ : Qcan=J.toContinuousLinearMap.range.starProjection := isometric_cogram_projection J
  rw [hQ]
  have he := metric_projection_excess_cogram M.change W J.toContinuousLinearMap.range hJW
  exact he ▸ isPositive_self_comp_adjoint (D.comp (W.starProjection-J.toContinuousLinearMap.range.starProjection))

#print axioms physical_source_excess_positive
end QuantitativeMaass.AdmissibleScalarCover
