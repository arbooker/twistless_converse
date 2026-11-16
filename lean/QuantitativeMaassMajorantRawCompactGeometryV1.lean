module

public import QuantitativeMaassMetricCapEnlargedWindowV1
public import QuantitativeMaassMovingBroadDeficitV1
public import QuantitativeMaassRawCompactGeometryCostV1
public import QuantitativeMaassMajorantCompactTraceV1
public import QuantitativeArithmeticMaassMovingCollarEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane AsymptoticFiniteBranch AsymptoticRegularTrace
open AsymptoticClassicalPetersson QuantitativeHolomorphic
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

def enlargedCompactMetricTraceError (N : ℕ) (M : ScalarCylinderMetric N)
    (δ C : ℝ) (hδ : 0<δ) (ν : ℕ) (E : Expression)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (t : ℝ) : ℝ :=
  let R := C*radius ε t
  let J := ⌈(ν:ℝ)*R+1⌉₊
  let a := movingLowerEdge δ C ε t
  let S := cutoffRectangle a t
  let hS := upperRectangle_compact 0 1 a _ (movingLowerEdge_pos hδ C ε t)
  let Pc := AsymptoticRegionL2.projection (quotientMeasure 0) S hS.measurableSet
  let L := (terminalInverseWeightBand δ ν J).comp M.change.symm.toContinuousLinearMap
  let Z := cylinderZeroExtension.toContinuousLinearMap
  let F := compactInputExpression S hS.measurableSet (metricCappedExpression M δ ν J E)
  columnLinearTrace (quotientMeasure 0) (fun z => Pc (enlargedWindowColumn K hc he ε t z))
    (L.comp ((Z.adjoint.comp ((holomorphicSum E 0).comp Z)).comp L.adjoint))-
    (∫ x in S,(matrix (regularSum F x) 1 1*
      windowIdentityContribution K hc (radius ε t) (radius_pos ε t)
        (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))).re)

def originalMajorantCompactMetricTraceError (N : ℕ) (M : ScalarCylinderMetric N)
    (δ C : ℝ) (hδ : 0<δ) (ν : ℕ) (E : Expression)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (t : ℝ) : ℝ :=
  let R := C*radius ε t
  let J := ⌈(ν:ℝ)*R+1⌉₊
  let a := movingLowerEdge δ C ε t
  let S := cutoffRectangle a t
  let hS := upperRectangle_compact 0 1 a _ (movingLowerEdge_pos hδ C ε t)
  let Pc := AsymptoticRegionL2.projection (quotientMeasure 0) S hS.measurableSet
  let L := (terminalInverseWeightBand δ ν J).comp M.change.symm.toContinuousLinearMap
  let Z := cylinderZeroExtension.toContinuousLinearMap
  let F := compactInputExpression S hS.measurableSet (metricCappedExpression M δ ν J E)
  columnLinearTrace (quotientMeasure 0) (fun z => Pc (originalMajorantColumn K hc he ε t z))
    (L.comp ((Z.adjoint.comp ((holomorphicSum E 0).comp Z)).comp L.adjoint))-
    (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹^2*(∫ x in S,(matrix (regularSum F x) 1 1*
      windowIdentityContribution K hc (radius ε t) (radius_pos ε t)
        (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))).re)

/-- The finite-filter geometric error uses the actual enlarged packet
and the actual raw expression horizon, including inverse-cap costs. -/
theorem originalMajorant_raw_compact_geometry_limit {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (N : ℕ) (M : ScalarCylinderMetric N) (δ C : ℝ) (hδ : 0<δ) (hC : 1≤C) (ν : ℕ)
    (E : ℕ→Expression) (B : ℝ) (hB : 0≤B)
    (hmass : ∀ n,expressionBound (E n)≤Real.exp (Real.exp (B*(4:ℝ)^n)))
    (hmatrix : ∀ n,ExpressionMatrixBound (E n) (Real.exp (Real.exp (B*(4:ℝ)^n))))
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => originalMajorantCompactMetricTraceError N M δ C hδ ν
      (E (rawBlockHorizon t)) K hc he ε t/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨U,D,hU,hD,hbound⟩ := metric_cap_enlarged_window_regular_comparison K he hc I
  have hcost := raw_compact_geometric_cost ε hε hp ν C ((M.lower⁻¹)^2) B D U hC
    (sq_nonneg _) hB hD.le
  have hgeom : Tendsto (fun t => enlargedCompactMetricTraceError N M δ C hδ ν
      (E (rawBlockHorizon t)) K hc he ε t/(t*ε t)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hcost
    filter_upwards [hε,eventually_ge_atTop (1:ℝ),
      movingCutoffRectangle_ball hδ C (zero_le_one.trans hC) ε hε hp,
      QuantitativeNinaMaass.originalWindowMajorant_parameters ε hε hp] with t heps ht hball hparam
    let a := movingLowerEdge δ C ε t
    let J := ⌈(ν:ℝ)*(C*radius ε t)+1⌉₊
    let m := Real.exp (Real.exp (B*(4:ℝ)^rawBlockHorizon t))
    have hb := hbound M δ ν J basis a (Real.exp (Strong.strongScale t/2))
      (movingLowerEdge_pos hδ C ε t) (E (rawBlockHorizon t)) m (Real.exp_pos _).le
      (hmatrix _) (4*Strong.strongScale t) (radius ε t) (ε t) t
      (smoothingWidth (slowScale t) (ε t)) (le_max_left _ _)
      (mul_nonneg (by norm_num) (sq_nonneg _)) heps.1.le heps.2 ht hparam.1.le hparam.2.1 hball
    change |enlargedCompactMetricTraceError N M δ C hδ ν (E (rawBlockHorizon t)) K hc he ε t|≤
      ((((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2*(M.lower⁻¹)^2*expressionBound (E (rawBlockHorizon t)))*
        (1+128*m)^40*D*Real.sqrt t*(ε t)^2*Real.exp (U*radius ε t+30*(4*Strong.strongScale t)) at hb
    rw [norm_div,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (mul_pos (zero_lt_one.trans_le ht) heps.1)]
    apply div_le_div_of_nonneg_right _ (mul_pos (zero_lt_one.trans_le ht) heps.1).le
    apply hb.trans
    rw [show 30*(4*Strong.strongScale t)=120*Strong.strongScale t by ring]
    gcongr
    exact hmass _
  have hlim := (originalMajorant_normalization_sq_limit K ε (hε.mono (fun _ h => h.1)) hp).mul hgeom
  rw [mul_zero] at hlim
  convert hlim using 1
  funext t
  dsimp only [originalMajorantCompactMetricTraceError,enlargedCompactMetricTraceError]
  rw [originalMajorant_localized_trace_eq]
  ring

#print axioms originalMajorant_raw_compact_geometry_limit
end QuantitativeMaass.Scheduled
