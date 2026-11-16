module

public import QuantitativeMaassRawReconstructedSourceErrorV1
public import QuantitativeMaassRawMetricSourceV1
public import QuantitativeMaassScalarMetricPhysicalV1
public import QuantitativeMaassMetricPowerExpressionV1
public import QuantitativeMaassContractiveTargetMinorantV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns ContinuousLinearMap
open AsymptoticFiniteBranch MeasureTheory
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)

def physicalSourceProjection : AsymptoticHyperbolicSlash.Space→L[ℂ]AsymptoticHyperbolicSlash.Space :=
  let V := (EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e).toContinuousLinearMap
  V.comp ((terminalSourceProjection A P e).comp V.adjoint)

theorem physicalSourceProjection_isProjection : IsStarProjection (physicalSourceProjection A P e) :=
  isometric_projection_conjugate (EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e)
    (terminalSourceProjection A P e)
    ⟨terminalSourceProjection_idempotent A P e,terminalSourceProjection_selfAdjoint A P e⟩

def physicalSource : Submodule ℂ AsymptoticHyperbolicSlash.Space := (physicalSourceProjection A P e).range

instance physicalSource_complete : CompleteSpace (physicalSource A P e) :=
  (physicalSourceProjection_isProjection A P e).isIdempotentElem.isClosed_range.completeSpace_coe

theorem physicalSourceProjection_eq : physicalSourceProjection A P e=(physicalSource A P e).starProjection :=
  (isStarProjection_iff_eq_starProjection_range.mp (physicalSourceProjection_isProjection A P e)).choose_spec

def physicalMetricSource (M : ScalarCylinderMetric N) : Submodule ℂ AsymptoticHyperbolicSlash.Space :=
  (physicalSource A P e).map M.physicalChange.toLinearMap

instance physicalMetricSource_complete (M : ScalarCylinderMetric N) :
    CompleteSpace (physicalMetricSource A P e M) :=
  (metric_image_closed M.physicalChange (physicalSource A P e)
    (physicalSourceProjection_isProjection A P e).isIdempotentElem.isClosed_range).completeSpace_coe

theorem reconstructedFilterExpression_physical_order (s : ℝ) (T : Expression)
    (hT : 0≤holomorphicSum T 0) (hT1 : holomorphicSum T 0≤1) :
    0≤holomorphicSum (reconstructedFilterExpression A P e s T) 0 ∧
      holomorphicSum (reconstructedFilterExpression A P e s T) 0≤1 := by
  rw [reconstructedFilterExpression_physical]
  exact contractive_target_minorant 1 (by change star (1 : AsymptoticHyperbolicSlash.Space→L[ℂ]AsymptoticHyperbolicSlash.Space)=1; exact star_one _) (by simp)
    (holomorphicSum (expression A P (NeZero.pos N) s e) 0) (physical_norm A P (NeZero.pos N) s e)
    (by rfl) _ hT hT1

/-- The actual finite common branch polynomial used to recover the metric
image of the all-row original source. -/
def physicalMetricFilterExpression (M : ScalarCylinderMetric N) (s : ℝ) (T : Expression) (m : ℕ) : Expression :=
  metricPowerExpression [M.branch] (reconstructedFilterExpression A P e s T) m

theorem physicalMetricFilterExpression_order (M : ScalarCylinderMetric N) (s : ℝ) (T : Expression)
    (hT : 0≤holomorphicSum T 0) (hT1 : holomorphicSum T 0≤1) (m : ℕ) :
    0≤holomorphicSum (physicalMetricFilterExpression A P e M s T m) 0 ∧
      holomorphicSum (physicalMetricFilterExpression A P e M s T m) 0≤1 := by
  have hh := reconstructedFilterExpression_physical_order A P e s T hT hT1
  exact metricPowerExpression_physical_order _ _ hh.1 hh.2 m

/-- Quantitative source recovery for the literal finite polynomial. Its
source is the actual closed image of all original rows, not an assumed
cuspidal or automorphic solution space. -/
theorem physicalMetricFilterExpression_source_error (M : ScalarCylinderMetric N) (s : ℝ) (T : Expression)
    (hT : 0≤holomorphicSum T 0) (hT1 : holomorphicSum T 0≤1)
    {δ : ℝ} (hδ : ‖holomorphicSum T 0*originalSourceProjection A P e-originalSourceProjection A P e‖≤δ)
    (m : ℕ) :
    let Qsrc := (physicalMetricSource A P e M).starProjection
    ‖holomorphicSum (physicalMetricFilterExpression A P e M s T m) 0*Qsrc-Qsrc‖^2≤
      ‖M.physicalChange.symm.toContinuousLinearMap‖^2/
        (expressionMetricScale [M.branch]*(((2*m:ℕ):ℝ)+1))+
      3*‖M.physicalChange.symm.toContinuousLinearMap‖^2*(δ+Real.exp (-8*s))*
        ‖M.physicalChange.toContinuousLinearMap‖^2 := by
  intro Qsrc
  let : CompleteSpace ((physicalSource A P e).map M.physicalChange.toLinearMap) :=
    physicalMetricSource_complete A P e M
  have hTn : ‖holomorphicSum T 0‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hT).mpr hT1
  have he := reconstructedFilterExpression_source_error A P e s T hTn hδ
  change ‖(holomorphicSum (reconstructedFilterExpression A P e s T) 0).comp
    (physicalSourceProjection A P e)-physicalSourceProjection A P e‖≤δ+Real.exp (-8*s) at he
  rw [physicalSourceProjection_eq] at he
  have horder := reconstructedFilterExpression_physical_order A P e s T hT hT1
  have hscale : expressionMetricScale [M.branch]*‖M.physicalChange.toContinuousLinearMap‖^2≤1 := by
    rw [←M.physicalChange_branch]
    exact expressionMetricScale_bound _ (norm_nonneg _) (holomorphicSum_norm_le _ 0)
  have hh := scaled_metric_image_source_error M.physicalChange (physicalSource A P e)
    (holomorphicSum (reconstructedFilterExpression A P e s T) 0) horder.1 horder.2 he
    (expressionMetricScale_pos [M.branch]) hscale m
  change ‖holomorphicSum (metricPowerExpression [M.branch] (reconstructedFilterExpression A P e s T) m) 0*
    (physicalMetricSource A P e M).starProjection-(physicalMetricSource A P e M).starProjection‖^2≤_
  rw [metricPowerExpression_physical,M.physicalChange_branch]
  exact hh

#print axioms physicalSourceProjection_isProjection
#print axioms reconstructedFilterExpression_physical_order
#print axioms physicalMetricFilterExpression_order
#print axioms physicalMetricFilterExpression_source_error
end QuantitativeMaass.RawCommonReconstruction
