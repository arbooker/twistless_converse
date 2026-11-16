module

public import QuantitativeMaassRawPhysicalMetricFilterV1
public import QuantitativeMaassFullExcessExpressionV1
public import QuantitativeMaassColumnSourceFilterV1

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open ContinuousLinearMap MeasureTheory AsymptoticClassicalPetersson
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
namespace QuantitativeMaass.RawCommonReconstruction
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q}
  (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)

/-- The actual all-row source projections agree under zero extension. -/
theorem sourceProjection_zeroExtension :
    (physicalSourceProjection A P e).comp cylinderZeroExtension.toContinuousLinearMap=
      cylinderZeroExtension.toContinuousLinearMap.comp (cylinderSourceProjection A P e) := by
  exact isometric_source_projection_intertwines cylinderZeroExtension
    (fullTerminalTranslationIsometry A (NeZero.pos N) P e).toContinuousLinearMap
    (EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e).toContinuousLinearMap
    (terminalSourceProjection A P e) (fullTerminalTranslation_physical A (NeZero.pos N) P e)

/-- Every vector of the concrete metric cylinder source lies in the physical
metric source after zero extension. -/
theorem metricCylinderSource_zeroExtension_mem (M : ScalarCylinderMetric N)
    (x : Lp ℂ 2 (quotientMeasure 0)) (hx : x∈metricCylinderSource A P e M.change) :
    cylinderZeroExtension x∈physicalMetricSource A P e M := by
  obtain ⟨y,hy,rfl⟩ := hx
  obtain ⟨v,rfl⟩ := hy
  refine ⟨cylinderZeroExtension (cylinderSourceProjection A P e v),?_,?_⟩
  · refine ⟨cylinderZeroExtension v,?_⟩
    exact DFunLike.congr_fun (sourceProjection_zeroExtension A P e) v
  · exact M.physicalChange_zeroExtension _

/-- Compression of a physical finite filter preserves its source error on
the actual cylinder source. -/
theorem physical_filter_cylinder_error (M : ScalarCylinderMetric N)
    (F : AsymptoticHyperbolicSlash.Space→L[ℂ]AsymptoticHyperbolicSlash.Space)
    {δ : ℝ} (hδ : ‖F*(physicalMetricSource A P e M).starProjection-
      (physicalMetricSource A P e M).starProjection‖≤δ) :
    let Z := cylinderZeroExtension.toContinuousLinearMap
    let Qc := (metricCylinderSource A P e M.change).starProjection
    ‖(Z.adjoint.comp (F.comp Z))*Qc-Qc‖≤δ := by
  intro Z Qc
  let Qp := (physicalMetricSource A P e M).starProjection
  have hfix : Qp.comp (Z.comp Qc)=Z.comp Qc := by
    apply ContinuousLinearMap.ext
    intro x
    exact Submodule.starProjection_eq_self_iff.mpr
      (metricCylinderSource_zeroExtension_mem A P e M _
        ((metricCylinderSource A P e M.change).starProjection_apply_mem x))
  exact isometric_filter_source_error cylinderZeroExtension Qc Qp F
    (metricCylinderSource A P e M.change).starProjection_norm_le hfix hδ

#print axioms sourceProjection_zeroExtension
#print axioms metricCylinderSource_zeroExtension_mem
#print axioms physical_filter_cylinder_error
end QuantitativeMaass.RawCommonReconstruction
