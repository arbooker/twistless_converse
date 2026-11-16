module

public import QuantitativeMaassFinitePowerTraceV1
public import QuantitativeMaassMetricPowerSandwichV1
public import QuantitativeMaassTerminalPowerFiniteV1
public import QuantitativeMaassRawPhysicalMetricFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped ENNReal
namespace QuantitativeMaass.RawCommonReconstruction
open AsymptoticFiniteBranch AsymptoticRegularTrace MeasureTheory
open QuantitativeEulerEndpointRegularBase QuantitativeEulerEndpointTerminalAlgebra
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
    (M : ScalarCylinderMetric N) (s : ℝ) (T : Expression)
    (hT : ∀ x,0≤regularSum T x ∧ regularSum T x≤1)
    (hl : ∀ x,AsymptoticOrbitDiagonal.corner (terminalRegion A P) x*regularSum T x=regularSum T x)
    (hr : ∀ x,regularSum T x*AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=regularSum T x)

include hT in
theorem physicalMetricFilterExpression_regular_order (m : ℕ) (x : UpperHalfPlane) :
    0≤regularSum (physicalMetricFilterExpression A P e M s T m) x ∧
      regularSum (physicalMetricFilterExpression A P e M s T m) x≤1 := by
  have hrec : 0≤regularSum (reconstructedFilterExpression A P e s T) x ∧
      regularSum (reconstructedFilterExpression A P e s T) x≤1 := by
    rw [reconstructedFilterExpression_regular]
    exact contractive_target_minorant 1
      (by change star (1 : RegularSpace→L[ℂ]RegularSpace)=1; exact star_one _) (by simp)
      (regularSum (expression A P (NeZero.pos N) s e) x) (regular_norm A P (NeZero.pos N) s e x)
      (by rfl) _ (hT x).1 (hT x).2
  exact metricPowerExpression_regular_order _ _ x hrec.1 hrec.2 m

include hT hl hr in
/-- The actual common metric expression satisfies the sharp terminal
regular trace estimate, with explicit polynomial-degree error costs. -/
theorem physicalMetricFilterExpression_regular_trace
    (F : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1) {δ : ℝ} (hδ : 0≤δ)
    (he : ∀ x,‖regularSum T x-rep A P F x‖≤δ) (m : ℕ) :
    signedTrace volume (regularSum (physicalMetricFilterExpression A P e M s T m))≤
      tr A P F+4*((m:ℝ)+1)*tr A P (F-F^2)+(12*(m:ℝ)+13)*‖tr A P‖*δ := by
  let R := expression A P (NeZero.pos N) s e
  let U := metricReconstructionExpression [M.branch] R
  have hU := metricReconstructionExpression_norm [M.branch] R (regular_norm A P (NeZero.pos N) s e)
  have hsource := metricReconstructionExpression_right A P [M.branch] R
    (regular_right_terminal A P (NeZero.pos N) s e)
  have hh := finite_regular_power_trace_bound A P U hU hsource T hT hl hr F hF0 hF1 hδ he m
  have hid : regularSum (physicalMetricFilterExpression A P e M s T m)=
      (fun x => 1-(1-regularSum U x*regularSum T x*(regularSum U x).adjoint)^m) := by
    funext x
    exact metricPowerExpression_sandwich [M.branch] R T m x
  rw [hid]
  exact hh

include hT hl hr in
/-- Cutoffs can be removed only after establishing finiteness of the
actual positive polynomial trace. -/
theorem physicalMetricFilterExpression_regular_finite (m : ℕ) :
    trace volume (regularSum (physicalMetricFilterExpression A P e M s T m))<∞ := by
  let R := expression A P (NeZero.pos N) s e
  let U := metricReconstructionExpression [M.branch] R
  let F := terminalFiniteElement A P T hT hl hr
  have hU := metricReconstructionExpression_norm [M.branch] R (regular_norm A P (NeZero.pos N) s e)
  have hsource := metricReconstructionExpression_right A P [M.branch] R
    (regular_right_terminal A P (NeZero.pos N) s e)
  have hh := regular_power_trace_finite A P U hU hsource F m
  have hid : regularSum (physicalMetricFilterExpression A P e M s T m)=
      (fun x => 1-(1-regularSum U x*rep A P F x*(regularSum U x).adjoint)^m) := by
    funext x
    exact metricPowerExpression_sandwich [M.branch] R T m x
  rw [hid]
  exact hh

include hT hl hr in
theorem physicalMetricFilterExpression_retained_trace
    (F : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1) {δ : ℝ} (hδ : 0≤δ)
    (he : ∀ x,‖regularSum T x-rep A P F x‖≤δ) (m : ℕ) (Y H : ℝ) :
    signedTrace volume (regularSum (retainedExpression Y H (physicalMetricFilterExpression A P e M s T m)))≤
      tr A P F+4*((m:ℝ)+1)*tr A P (F-F^2)+(12*(m:ℝ)+13)*‖tr A P‖*δ := by
  have hcut := regularRetained_trace_le_full Y H
    (regularSum (physicalMetricFilterExpression A P e M s T m))
    (regularSum_matrix_measurable _) (fun x => ContinuousLinearMap.nonneg_iff_isPositive.mp
      (physicalMetricFilterExpression_regular_order A P e M s T hT m x).1)
    (physicalMetricFilterExpression_regular_finite A P e M s T hT hl hr m)
  have hid : regularSum (retainedExpression Y H (physicalMetricFilterExpression A P e M s T m))=
      regularRetained Y H (regularSum (physicalMetricFilterExpression A P e M s T m)) :=
    funext (regularSum_retainedExpression Y H _)
  rw [hid]
  exact hcut.trans (physicalMetricFilterExpression_regular_trace A P e M s T hT hl hr F hF0 hF1 hδ he m)

#print axioms physicalMetricFilterExpression_regular_order
#print axioms physicalMetricFilterExpression_retained_trace
#print axioms physicalMetricFilterExpression_regular_trace
#print axioms physicalMetricFilterExpression_regular_finite
end QuantitativeMaass.RawCommonReconstruction
