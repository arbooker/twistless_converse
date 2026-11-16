module

public import QuantitativeMaassCanonicalCapSpaceV1
public import QuantitativeMaassRawPhysicalMetricFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane ContinuousLinearMap AsymptoticSectorSigns AsymptoticFiniteBranch
open FinitenessCertificate FinitenessGlobalHeight
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups
local instance (N : ℕ) [NeZero N] : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := Fintype.ofFinite _
namespace QuantitativeMaass.AdmissibleScalarCover
variable {N : ℕ} [NeZero N] {hN : GridAdmissibleGap.Admissible N}
    (C : AdmissibleScalarCover N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)

instance regularCapSpace_metric_complete (e : Sector N) (z : ℍ) :
    CompleteSpace ((C.regularCapSpace hδ hν e z).map ((C.metric hδ hν).regularChange z).toLinearMap) :=
  (metric_image_closed ((C.metric hδ hν).regularChange z) _
    (C.regularCapSpace_closed hδ hν e z)).completeSpace_coe

/-- The metric image of the closed raw cap space is exactly the canonical
regular projection whose incidence trace was computed. -/
theorem regularCapSpace_metric_projection (e : Sector N) (z : ℍ) :
    ((C.regularCapSpace hδ hν e z).map ((C.metric hδ hν).regularChange z).toLinearMap).starProjection=
      C.regularProjection hδ hν e z := by
  have hc := CountingMetric.regularCanonicalProjection_cogram N C.family hδ C.height_pos hν C.covers hN C.member e z
  change C.regularProjection hδ hν e z=
    (C.regularIsometry hδ hν e z).toContinuousLinearMap.comp
      (C.regularIsometry hδ hν e z).toContinuousLinearMap.adjoint at hc
  rw [hc,AsymptoticIsometryRange.cogram]
  simp only [C.regularCapSpace_metric_image hδ hν e z]

/-- Scalar metric transport of a proved raw canonical approximation.
The output is the actual finite branch expression and actual canonical projection. -/
theorem regular_metric_power_error (e : Sector N) (z : ℍ) (F : Expression)
    (hF : 0≤regularSum F z) (hF1 : regularSum F z≤1) {η : ℝ}
    (hη : ‖regularSum F z*(C.regularCapSpace hδ hν e z).starProjection-
      (C.regularCapSpace hδ hν e z).starProjection‖≤η) (m : ℕ) :
    let M := C.metric hδ hν
    ‖regularSum (metricPowerExpression [M.branch] F m) z*C.regularProjection hδ hν e z-
      C.regularProjection hδ hν e z‖^2≤
      ‖(M.regularChange z).symm.toContinuousLinearMap‖^2/
        (expressionMetricScale [M.branch]*(((2*m:ℕ):ℝ)+1))+
      3*‖(M.regularChange z).symm.toContinuousLinearMap‖^2*η*
        ‖(M.regularChange z).toContinuousLinearMap‖^2 := by
  intro M
  have hscale : expressionMetricScale [M.branch]*‖(M.regularChange z).toContinuousLinearMap‖^2≤1 := by
    rw [←M.regularChange_branch z]
    exact expressionMetricScale_bound _ (norm_nonneg _) (regularSum_norm_le _ z)
  have hh := scaled_metric_image_source_error (M.regularChange z)
    (C.regularCapSpace hδ hν e z) (regularSum F z) hF hF1 hη
    (expressionMetricScale_pos [M.branch]) hscale m
  rw [C.regularCapSpace_metric_projection hδ hν e z] at hh
  rw [metricPowerExpression_regular,M.regularChange_branch]
  exact hh

#print axioms regularCapSpace_metric_projection
#print axioms regular_metric_power_error
end QuantitativeMaass.AdmissibleScalarCover
