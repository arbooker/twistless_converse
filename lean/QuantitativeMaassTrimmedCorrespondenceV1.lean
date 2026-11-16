module

public import QuantitativeMaassTranslatedCorrespondenceV1
public import QuantitativeMaassLogScaleGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeArithmeticMaassOverlap
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- For any fixed time translation and fixed positive integral correspondence, the actual nonscalar
quotient error is o(t epsilon(t)) for the literal trimmed interval [t+delta,t+epsilon(t)-delta]
with independent radii o(log t). No slow-scale restriction is imposed on these radii. -/
theorem translatedWindowIntegralRemainder_trimmed_negligible (s : ℝ) (N : ℕ) [NeZero N]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε R L : ℝ → ℝ) (hRp : ∀ t,0<R t) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (hR1 : ∀ᶠ t in atTop,1≤R t) (hLp : ∀ᶠ t in atTop,0≤L t)
    (hR : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0))
    (hL : Tendsto (fun t => L t/Real.log t) atTop (𝓝 0)) :
    Tendsto (fun t =>
      (∫ z in Metric.closedBall o (L t),‖translatedWindowIntegralRemainder s N M hM K hc
        (R t) (hRp t)
        (t+δ t) (t+ε t-δ t) z‖ ∂quotientMeasure N)/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := translatedWindowIntegralRemainder_exp_bound s M hM K he hc o
  have hmajor := geometric_majorant_log_tendsto ε R L
    A (2*C) hA.le (by positivity) hε
    (Eventually.of_forall (fun t => (hRp t).le)) hLp hR hL
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    exact div_nonneg (integral_nonneg (fun _ => norm_nonneg _)) (mul_pos ht he.1).le
  · filter_upwards [hε,hδ,hR1,hLp,eventually_ge_atTop (1:ℝ)] with t he hd hr hl ht
    have hεpos : 0<ε t := he.1
    have htpos : 0<t := lt_of_lt_of_le zero_lt_one ht
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hb := hbound N (L t) (R t) (ε t/2-δ t)
      (t+ε t/2) hr hl (by linarith [hd.2])
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
        Real.exp (A*R t+30*L t) := by gcongr
      _ = _ := by ring

#print axioms translatedWindowIntegralRemainder_trimmed_negligible

end QuantitativeMaass
