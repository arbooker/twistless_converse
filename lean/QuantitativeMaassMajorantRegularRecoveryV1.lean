module

public import QuantitativeMaassMetricCapRegularDifferenceV1
public import QuantitativeMaassRawInverseBandRecoveryV1
public import QuantitativeMaassMajorantTraceNormalizationV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane AsymptoticFiniteBranch AsymptoticRegularTrace
open AsymptoticRegularCompactBranch (Space)
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap ComplexConjugate ENNReal
namespace QuantitativeMaass.Scheduled

/-- The two literal regular integrals after inverse-cap/metric insertion. -/
def compactMetricRegularDifference {N : ℕ} (M : ScalarCylinderMetric N)
    (δ C : ℝ) (hδ : 0<δ) (ν : ℕ) (E : Expression) (Q : ℍ→Space→L[ℂ]Space)
    (ε : ℝ→ℝ) (t : ℝ) (w : ℂ) : ℝ :=
  let J := ⌈(ν:ℝ)*(C*radius ε t)+1⌉₊
  let a := movingLowerEdge δ C ε t
  let S := cutoffRectangle a t
  let hS := (upperRectangle_compact 0 1 a _ (movingLowerEdge_pos hδ C ε t)).measurableSet
  let F := compactInputExpression S hS (metricCappedExpression M δ ν J E)
  let k := metricCapCoefficient M δ ν J
  (∫ x in S,(matrix (regularSum F x) 1 1*w).re)-
    ∫ x in S,(k x*conj (k x)*matrix (Q x) 1 1*w).re

/-- Constructed weighted regular recovery survives localization and the
actual enlarged window contribution. The error is the raw geometric
recovery rate, not a strong-scale approximation assumption. -/
theorem originalMajorant_regular_recovery_limit {N : ℕ} (M : ScalarCylinderMetric N)
    (δ C : ℝ) (hδ : 0<δ) (hC : 1≤C) (ν : ℕ)
    (E : ℕ→Expression) (Q : ℍ→Space→L[ℂ]Space)
    (A D Kreg I : ℝ) (hD : 0≤D) (hKreg : 0≤Kreg) (hI : 0≤I)
    (hmQ : Measurable (fun x => matrix (Q x) 1 1))
    (hE : ∀ n x,‖regularSum (E n) x‖≤A) (hQ : ∀ x,‖Q x‖≤A)
    (hweighted : ∀ n (B : ℍ→Space→L[ℂ]Space) (L : ℝ),0≤L →
      (∀ a b,Measurable (fun x => matrix (B x) a b)) → Covariant B →
      (∀ x,‖B x‖≤L) → |signedTrace volume (fun x => B x*(regularSum (E n) x-Q x))|≤
        L*(D/(2:ℝ)^n+4*Real.sqrt (Kreg/(2:ℝ)^n)*I))
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹^2*
      compactMetricRegularDifference M δ C hδ ν (E (rawBlockHorizon t)) Q ε t
        (windowIdentityContribution K hc (radius ε t) (radius_pos ε t)
          (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t)))/(t*ε t))
      atTop (𝓝 0) := by
  let w := fun t => windowIdentityContribution K hc (radius ε t) (radius_pos ε t)
    (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))
  obtain ⟨B,hB,hwin⟩ := enlargedWindowIdentity_bound K he hc hK hm
  have hw : ∀ᶠ t in atTop,‖w t‖≤B*(t*ε t) := by
    filter_upwards [hε,eventually_ge_atTop (3:ℝ),radius_resolves_window ε hε hp,
      QuantitativeNinaMaass.originalWindowMajorant_parameters ε hε hp] with t heps ht hresolve hparam
    have hh := hwin (radius ε t) t (ε t)
      (t-smoothingWidth (slowScale t) (ε t))
      (t+ε t+smoothingWidth (slowScale t) (ε t)) (le_max_left _ _) (by linarith)
      heps.1.le heps.2 hresolve.2 hparam.2.2 (by linarith [hparam.1,heps.1])
      (by linarith [hparam.2.1,heps.2]) (by linarith [hparam.2.1])
    simpa only [w,mul_assoc] using hh
  have hcost := raw_inverse_band_window_recovery_decay ε hε hp ν C ((M.lower⁻¹)^2) D Kreg I B
    hC (sq_nonneg _) hD hKreg hI w hw
  have hdiff : Tendsto (fun t => compactMetricRegularDifference M δ C hδ ν
      (E (rawBlockHorizon t)) Q ε t (w t)/(t*ε t)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hcost
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    let J := ⌈(ν:ℝ)*(C*radius ε t)+1⌉₊
    let a := movingLowerEdge δ C ε t
    let S := cutoffRectangle a t
    have hS : IsCompact S := upperRectangle_compact 0 1 a _ (movingLowerEdge_pos hδ C ε t)
    have hh := metric_cap_local_regular_difference M δ ν J (E (rawBlockHorizon t)) Q
      (D/(2:ℝ)^rawBlockHorizon t+4*Real.sqrt (Kreg/(2:ℝ)^rawBlockHorizon t)*I)
      (hweighted _) hmQ A (hE _) hQ S hS.measurableSet hS.measure_lt_top (w t)
    change |compactMetricRegularDifference M δ C hδ ν (E (rawBlockHorizon t)) Q ε t (w t)|≤
      ((((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))*M.lower⁻¹)^2*‖w t‖*
        (D/(2:ℝ)^rawBlockHorizon t+4*Real.sqrt (Kreg/(2:ℝ)^rawBlockHorizon t)*I) at hh
    rw [norm_div,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (mul_pos ht heps.1)]
    apply (div_le_div_of_nonneg_right hh (mul_pos ht heps.1).le).trans_eq
    rw [mul_pow]
  have hlim := (originalMajorant_normalization_sq_limit K ε (hε.mono (fun _ h => h.1)) hp).mul hdiff
  rw [mul_zero] at hlim
  convert hlim using 1
  funext t
  ring

#print axioms originalMajorant_regular_recovery_limit
end QuantitativeMaass.Scheduled
