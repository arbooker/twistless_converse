module

public import QuantitativeMaassTrimmedGeometricErrorsV1
public import QuantitativeMaassTrimmedIdentityLimitV1
public import QuantitativeMaassParityLocalMainV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

theorem windowParity_local_trimmed_geometric_negligible {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (σ : ℝ) (hσ : σ^2=1) (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t) (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0)) :
    Tendsto (fun t =>
      |(∑' i,∫ x in Metric.closedBall o (R t),
        ‖(windowWavePacket N K hc (R t) (hRp t)
          (t+δ t) (t+ε t-δ t) (parityProjection N σ (b i))).val x‖^2 ∂quotientMeasure N)-
        (quotientMeasure N).real (Metric.closedBall o (R t))*
          (windowIdentityContribution K hc (R t) (hRp t)
            (t+δ t) (t+ε t-δ t)).re/2|/(t*ε t)) atTop (𝓝 0) := by
  have hG := windowGeometricRemainder_trimmed_negligible N K he hc o ε hε δ hδ R hRp hR1 hRlog
  have hH := windowReflection_trimmed_negligible N K he hc o ε hε δ hδ R hRp hR1 hRlog
  have hmajor := (hG.add hH).div_const 2
  simp only [zero_add,zero_div] at hmajor
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hp
    exact div_nonneg (abs_nonneg _) (mul_pos hp ht.1).le
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hp
    rw [(windowParity_local_real_trace N b _ (isCompact_closedBall o (R t))
      σ hσ K he hc (R t) (hRp t) (t+δ t) (t+ε t-δ t)).tsum_eq]
    calc
      _ ≤ ((∫ x in Metric.closedBall o (R t),
          ‖windowGeometricRemainder N K hc (R t) (hRp t)
            (t+δ t) (t+ε t-δ t) x‖ ∂quotientMeasure N)+
          ∫ x in Metric.closedBall o (R t),
          ‖windowReflection N K hc (R t) (hRp t)
            (t+δ t) (t+ε t-δ t) x‖ ∂quotientMeasure N)/2/(t*ε t) :=
        div_le_div_of_nonneg_right (windowParity_integral_error N _
          (isCompact_closedBall o (R t)) σ hσ K he hc
          (R t) (hRp t) (t+δ t) (t+ε t-δ t)) (mul_pos hp ht.1).le
      _ = _ := by ring


theorem windowParity_local_trimmed_trace_main {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (σ : ℝ) (hσ : σ^2=1) (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t) (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0))
    (hRtop : Tendsto R atTop atTop) (hRδ : ∀ᶠ t in atTop,1/R t≤δ t)
    (hsmall : Tendsto (fun t => δ t/ε t) atTop (𝓝 0))
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      (∑' i,∫ x in Metric.closedBall o (R t),
        ‖(windowWavePacket N K hc (R t) (hRp t)
          (t+δ t) (t+ε t-δ t) (parityProjection N σ (b i))).val x‖^2 ∂quotientMeasure N)/(t*ε t))
      atTop (𝓝 ((quotientMeasure N).real univ/(4*Real.pi))) := by
  let A := fun t => ∑' i,∫ x in Metric.closedBall o (R t),
    ‖(windowWavePacket N K hc (R t) (hRp t)
      (t+δ t) (t+ε t-δ t) (parityProjection N σ (b i))).val x‖^2 ∂quotientMeasure N
  let V := fun t => (quotientMeasure N).real (Metric.closedBall o (R t))
  let I := fun t => (windowIdentityContribution K hc (R t)
    (hRp t) (t+δ t) (t+ε t-δ t)).re
  have hgeom := windowParity_local_trimmed_geometric_negligible N b σ hσ K he hc o ε hε δ hδ R hRp hR1 hRlog
  have herr : Tendsto (fun t => A t/(t*ε t)-V t*(I t/(t*ε t))/2) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply hgeom.congr'
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hp
    change |A t-V t*I t/2|/(t*ε t)=‖A t/(t*ε t)-V t*(I t/(t*ε t))/2-0‖
    rw [sub_zero,show A t/(t*ε t)-V t*(I t/(t*ε t))/2=(A t-V t*I t/2)/(t*ε t) by ring,
      Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos hp ht.1)]
  have hV := quotientMeasure_expanding_ball_limit N o R hRtop
  have hI := windowIdentityContribution_trimmed_normalized K he hc hK hm ε hε δ hδ R hRp hR1 hRδ hsmall hproduct
  have hmain := (hV.mul hI).div_const 2
  change Tendsto (fun t => V t*(I t/(t*ε t))/2) atTop
    (𝓝 ((quotientMeasure N).real univ*(1/(2*Real.pi))/2)) at hmain
  have hh := herr.add hmain
  simp only [sub_add_cancel,zero_add] at hh
  convert hh using 1
  ring


#print axioms windowParity_local_trimmed_geometric_negligible
#print axioms windowParity_local_trimmed_trace_main

end QuantitativeMaass
