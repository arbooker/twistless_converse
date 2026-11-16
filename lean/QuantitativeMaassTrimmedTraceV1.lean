module

public import QuantitativeMaassTranslatedIdentityV1
public import QuantitativeMaassTrimmedCorrespondenceV1
public import QuantitativeMaassTrimmedIdentityLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ENNReal SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

attribute [local instance] Classical.propDecidable

/-- The signed error from the exact cosine-weighted spherical main term
is negligible for the actual trimmed interval. The oscillating main term
is retained explicitly; no unjustified scalar limit for it is asserted. -/
theorem translatedWindowIntegralKernel_trimmed_trace_error (τ : ℝ) (N : ℕ) [NeZero N]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t)
    (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0)) :
    Tendsto (fun t =>
      ((∫ x in Metric.closedBall o (R t),
        (translatedWindowIntegralKernel τ N M hM K hc (R t)
          (hRp t) (t+δ t) (t+ε t-δ t) x).re ∂quotientMeasure N)-
        (quotientMeasure N).real (Metric.closedBall o (R t))*
          (if integralIdentityCoset N M then (translatedWindowIdentity τ K hc (R t)
            (hRp t) (t+δ t) (t+ε t-δ t)).re else 0))/(t*ε t)) atTop (𝓝 0) := by
  have hgeom := translatedWindowIntegralRemainder_trimmed_negligible τ N M hM K he hc o ε R R hRp hε δ hδ
    hR1 (Eventually.of_forall (fun t => (hRp t).le)) hRlog hRlog
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hgeom
  filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hp
  rw [sub_zero,Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos hp ht.1)]
  exact div_le_div_of_nonneg_right (translatedWindowIntegralKernel_integral_error τ N M hM _
    (isCompact_closedBall o (R t)) K he hc _
    (hRp t) (t+δ t) (t+ε t-δ t)) (mul_pos hp ht.1).le

/-- Replacing expanding-ball volume by the full actual quotient volume costs
little-o of the original window normalization, even for oscillating shifts. -/
theorem translatedWindowIdentity_trimmed_volume_error (τ : ℝ) (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t)
    (hR1 : ∀ᶠ t in atTop,1≤R t) (hRtop : Tendsto R atTop atTop)
    (hRδ : ∀ᶠ t in atTop,1/R t≤δ t)
    (hsmall : Tendsto (fun t => δ t/ε t) atTop (𝓝 0))
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      (((quotientMeasure N).real (Metric.closedBall o (R t))-
        (quotientMeasure N).real univ)*
      (translatedWindowIdentity τ K hc (R t)
        (hRp t) (t+δ t) (t+ε t-δ t)).re)/(t*ε t)) atTop (𝓝 0) := by
  have hV := (quotientMeasure_expanding_ball_limit N o R hRtop).sub_const ((quotientMeasure N).real univ)
  rw [sub_self] at hV
  have hlim := hV.norm.mul (windowIdentityContribution_trimmed_normalized K he hc hK hm ε hε δ hδ R hRp hR1 hRδ hsmall hproduct)
  simp only [norm_zero,zero_mul] at hlim
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hε,hδ,eventually_gt_atTop (0:ℝ)] with t ht hd hp
  rw [norm_div,norm_mul,Real.norm_eq_abs (t*ε t),abs_of_pos (mul_pos hp ht.1),mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [Real.norm_eq_abs]
  exact div_le_div_of_nonneg_right
    (translatedWindowIdentity_abs_le τ K he hc hK hm _ (hRp t)
      (t+δ t) (t+ε t-δ t) (by linarith [hd.1]) (by linarith [hd.2])) (mul_pos hp ht.1).le

#print axioms translatedWindowIntegralKernel_trimmed_trace_error
#print axioms translatedWindowIdentity_trimmed_volume_error

end QuantitativeMaass
