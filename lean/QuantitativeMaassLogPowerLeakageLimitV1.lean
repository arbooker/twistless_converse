module

public import QuantitativeMaassLogPowerMarginV1
public import QuantitativeMaassPrincipalLeakageV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip
open scoped Topology SchwartzMap

namespace QuantitativeMaass

/-- The summed shell majorant is negligible on the original main-term scale,
using only the original triple-logarithmic width condition. -/
theorem logPower_leakage_majorant_tendsto (c : ℝ) (hc : 0<c) (C : ℝ) (hC : 0≤C)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => (C*(t+2)/(logPowerRadius c t*logPowerMargin c t)^4)/(t*ε t))
      atTop (𝓝 0) := by
  have hmajor : Tendsto (fun t => (3*C)*(logPowerMargin c t/ε t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (logPowerMargin_div_width c hc ε hε hproduct).const_mul (3*C)
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_ge_atTop (1:ℝ)] with t he ht
    positivity
  · filter_upwards [hε,eventually_ge_atTop (1:ℝ)] with t he ht
    have ht0 : 0<t := by linarith
    let Q := logPowerRadius (c/2) t
    have hQ : 0<Q := logPowerRadius_pos _ _
    have hQ1 : 1≤Q := le_max_left _ _
    have hQ4 : Q≤Q^4 := by
      have hh := pow_le_pow_right₀ hQ1 (show 1≤4 by omega)
      simpa only [pow_one] using hh
    rw [logPowerRadius_mul_margin]
    change (C*(t+2)/Q^4)/(t*ε t)≤_
    calc
      _ ≤ (C*(3*t)/Q^4)/(t*ε t) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith : t+2≤3*t) hC
      _ = (3*C)/(Q^4*ε t) := by field_simp
      _ ≤ (3*C)/(Q*ε t) := div_le_div_of_nonneg_left (by positivity)
        (mul_pos hQ he) (mul_le_mul_of_nonneg_right hQ4 he.le)
      _ = _ := by dsimp only [logPowerMargin,Q]; ring

/-- The actual sum over all principal cusp eigenvectors outside the literal
window is o(t epsilon) for the chosen logarithmic-power trimming margin. -/
theorem principal_trimmed_leakage_logPower_negligible {ι : Type*}
    (N : ℕ) (hN : 0<N) (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (c : ℝ) (hc : 0<c) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      (∑' i : {i // 1/4≤e i ∧ Real.sqrt (e i-1/4)∉Icc t (t+ε t)},
        (smoothedWindow K (logPowerRadius c t)
          (Icc (t+logPowerMargin c t) (t+ε t-logPowerMargin c t)∪
            Icc (-(t+ε t-logPowerMargin c t)) (-(t+logPowerMargin c t)))
          (Real.sqrt (e i.val-1/4)))^2)/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := principal_trimmed_window_leakage N hN
  have hmajor := logPower_leakage_majorant_tendsto c hc (C*(∫ u,|u|^2*K u)^2)
    (by positivity) ε (hε.mono (fun _ h => h.1)) hproduct
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t het ht
    exact div_nonneg (tsum_nonneg (fun i => sq_nonneg _)) (mul_nonneg ht.le het.1.le)
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t het ht
    have hh := (hbound ι v hv hcusp e he hgraph K hK t (ε t) (logPowerMargin c t)
      (logPowerRadius c t) ht het.2 (logPowerMargin_pos _ _) (logPowerMargin_le_one _ _)
      (logPowerRadius_pos _ _)).2
    exact div_le_div_of_nonneg_right hh (mul_nonneg ht.le het.1.le)

#print axioms logPower_leakage_majorant_tendsto
#print axioms principal_trimmed_leakage_logPower_negligible

end QuantitativeMaass
