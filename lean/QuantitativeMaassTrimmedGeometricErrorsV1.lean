module

public import QuantitativeMaassLogScaleGeometryV1
public import QuantitativeMaassReflectionLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- Actual trimmed-window geometric error for any positive radius o(log t). -/
theorem windowGeometricRemainder_trimmed_negligible (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t) (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0)) :
    Tendsto (fun t =>
      (∫ z in Metric.closedBall o (R t),‖windowGeometricRemainder N K hc
        (R t) (hRp t)
        (t+δ t) (t+ε t-δ t) z‖ ∂quotientMeasure N)/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := windowGeometricRemainder_exp_bound K he hc o
  have hmajor := geometric_majorant_log_tendsto ε R R A (2*C) hA.le (by positivity) hε
    (Eventually.of_forall (fun t => (hRp t).le)) (Eventually.of_forall (fun t => (hRp t).le)) hRlog hRlog
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    exact div_nonneg (integral_nonneg (fun _ => norm_nonneg _)) (mul_pos ht he.1).le
  · filter_upwards [hε,hδ,hR1,eventually_ge_atTop (1:ℝ)] with t he hd hr ht
    have hεpos : 0<ε t := he.1
    have htpos : 0<t := lt_of_lt_of_le zero_lt_one ht
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hb := hbound N (R t) (R t) (ε t/2-δ t)
      (t+ε t/2) hr (hRp t).le (by linarith [hd.2])
      (by linarith [hd.1]) (by linarith)
    rw [show t+ε t/2-(ε t/2-δ t)=t+δ t by ring,show t+ε t/2+(ε t/2-δ t)=t+ε t-δ t by ring] at hb
    apply hb.trans
    have hs : Real.sqrt (t+ε t/2)≤2*Real.sqrt t := by
      have ht0 : 0≤t := by linarith
      have hts : 0≤t+ε t/2 := by positivity
      nlinarith [Real.sq_sqrt ht0,Real.sq_sqrt hts,Real.sqrt_nonneg t,Real.sqrt_nonneg (t+ε t/2)]
    have hw : (ε t/2-δ t)^2≤(ε t)^2 :=
      pow_le_pow_left₀ (by linarith [hd.2]) (by linarith [hd.1]) 2
    calc
      _ ≤ C*(2*Real.sqrt t)*(ε t)^2*
        Real.exp (A*R t+30*R t) := by gcongr
      _ = _ := by ring

/-- Actual trimmed-window geometric error for any positive radius o(log t). -/
theorem windowReflection_trimmed_negligible (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t) (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0)) :
    Tendsto (fun t =>
      (∫ z in Metric.closedBall o (R t),‖windowReflection N K hc
        (R t) (hRp t)
        (t+δ t) (t+ε t-δ t) z‖ ∂quotientMeasure N)/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := windowReflection_exp_bound K he hc o
  have hmajor := geometric_majorant_log_tendsto ε R R A (2*C) hA.le (by positivity) hε
    (Eventually.of_forall (fun t => (hRp t).le)) (Eventually.of_forall (fun t => (hRp t).le)) hRlog hRlog
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    exact div_nonneg (integral_nonneg (fun _ => norm_nonneg _)) (mul_pos ht he.1).le
  · filter_upwards [hε,hδ,hR1,eventually_ge_atTop (1:ℝ)] with t he hd hr ht
    have hεpos : 0<ε t := he.1
    have htpos : 0<t := lt_of_lt_of_le zero_lt_one ht
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hb := hbound N (R t) (R t) (ε t/2-δ t)
      (t+ε t/2) hr (hRp t).le (by linarith [hd.2])
      (by linarith [hd.1]) (by linarith)
    rw [show t+ε t/2-(ε t/2-δ t)=t+δ t by ring,show t+ε t/2+(ε t/2-δ t)=t+ε t-δ t by ring] at hb
    apply hb.trans
    have hs : Real.sqrt (t+ε t/2)≤2*Real.sqrt t := by
      have ht0 : 0≤t := by linarith
      have hts : 0≤t+ε t/2 := by positivity
      nlinarith [Real.sq_sqrt ht0,Real.sq_sqrt hts,Real.sqrt_nonneg t,Real.sqrt_nonneg (t+ε t/2)]
    have hw : (ε t/2-δ t)^2≤(ε t)^2 :=
      pow_le_pow_left₀ (by linarith [hd.2]) (by linarith [hd.1]) 2
    calc
      _ ≤ C*(2*Real.sqrt t)*(ε t)^2*
        Real.exp (A*R t+30*R t) := by gcongr
      _ = _ := by ring



#print axioms windowGeometricRemainder_trimmed_negligible
#print axioms windowReflection_trimmed_negligible

end QuantitativeMaass
