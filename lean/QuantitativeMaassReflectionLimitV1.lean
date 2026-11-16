module

public import QuantitativeMaassReflectionGrowthV1
public import QuantitativeMaassGeometricLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- The literal original quotient reflected kernel is o(t epsilon(t)) on
any centre balls whose radii are negligible relative to the slow scale.
The propagation radius is constructed from the original width hypotheses. -/
theorem windowReflection_negligible (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε L : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hLp : ∀ᶠ t in atTop,0≤L t)
    (hL : Tendsto (fun t => L t/slowScale t) atTop (𝓝 0)) :
    Tendsto (fun t =>
      (∫ z in Metric.closedBall o (L t),‖windowReflection N K hc
        (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
        (t-ε t) (t+ε t) z‖ ∂quotientMeasure N)/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := windowReflection_exp_bound K he hc o
  have hεp : ∀ᶠ t in atTop,0<ε t := hε.mono (fun _ h => h.1)
  have hmajor := geometric_majorant_tendsto ε (positiveWindowRadius ε) L A C hA.le hC.le hε
    (Eventually.of_forall (fun t => (positiveWindowRadius_pos ε t).le)) hLp
    (positiveWindowRadius_div_scale ε hεp hproduct) hL
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    exact div_nonneg (integral_nonneg (fun _ => norm_nonneg _)) (mul_pos ht he.1).le
  · filter_upwards [hε,hLp,eventually_ge_atTop (1:ℝ)] with t he hl ht
    have hεpos : 0<ε t := he.1
    have htpos : 0<t := lt_of_lt_of_le zero_lt_one ht
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact hbound N (L t) (positiveWindowRadius ε t) (ε t) t (le_max_left _ _) hl he.1.le he.2 ht

/-- With the same constructed radius for propagation and centre balls, no
additional geometric schedule hypothesis remains. -/
theorem windowReflection_chosen_negligible (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      (∫ z in Metric.closedBall o (positiveWindowRadius ε t),‖windowReflection N K hc
        (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
        (t-ε t) (t+ε t) z‖ ∂quotientMeasure N)/(t*ε t)) atTop (𝓝 0) :=
  windowReflection_negligible N K he hc o ε (positiveWindowRadius ε) hε hproduct
    (Eventually.of_forall (fun t => (positiveWindowRadius_pos ε t).le))
    (positiveWindowRadius_div_scale ε (hε.mono (fun _ h => h.1)) hproduct)

/-- The same original-hypothesis little-o estimate for the literal manuscript
interval [t,t+epsilon(t)], with no shifted-width or extra radius assumption. -/
theorem windowReflection_interval_negligible (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      (∫ z in Metric.closedBall o (positiveWindowRadius ε t),‖windowReflection N K hc
        (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
        t (t+ε t) z‖ ∂quotientMeasure N)/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := windowReflection_exp_bound K he hc o
  have hεp := hε.mono (fun _ h => h.1)
  have hR := positiveWindowRadius_div_scale ε hεp hproduct
  have hRp : ∀ᶠ t in atTop,0≤positiveWindowRadius ε t :=
    Eventually.of_forall (fun t => (positiveWindowRadius_pos ε t).le)
  have hmajor := geometric_majorant_tendsto ε (positiveWindowRadius ε) (positiveWindowRadius ε)
    A (2*C) hA.le (by positivity) hε hRp hRp hR hR
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    exact div_nonneg (integral_nonneg (fun _ => norm_nonneg _)) (mul_pos ht he.1).le
  · filter_upwards [hε,eventually_ge_atTop (1:ℝ)] with t he ht
    have hεpos : 0<ε t := he.1
    have htpos : 0<t := lt_of_lt_of_le zero_lt_one ht
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hb := hbound N (positiveWindowRadius ε t) (positiveWindowRadius ε t) (ε t/2)
      (t+ε t/2) (le_max_left _ _) (positiveWindowRadius_pos ε t).le (by positivity)
      (by linarith) (by linarith)
    rw [show t+ε t/2-ε t/2=t by ring,show t+ε t/2+ε t/2=t+ε t by ring] at hb
    apply hb.trans
    have hs : Real.sqrt (t+ε t/2)≤2*Real.sqrt t := by
      have ht0 : 0≤t := by linarith
      have hts : 0≤t+ε t/2 := by positivity
      nlinarith [Real.sq_sqrt ht0,Real.sq_sqrt hts,Real.sqrt_nonneg t,Real.sqrt_nonneg (t+ε t/2)]
    have hw : (ε t/2)^2≤(ε t)^2 := by nlinarith [sq_nonneg (ε t)]
    calc
      _ ≤ C*(2*Real.sqrt t)*(ε t)^2*
        Real.exp (A*positiveWindowRadius ε t+30*positiveWindowRadius ε t) := by gcongr
      _ = _ := by ring


#print axioms windowReflection_negligible
#print axioms windowReflection_chosen_negligible
#print axioms windowReflection_interval_negligible

end QuantitativeMaass
