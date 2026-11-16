module

public import QuantitativeMaassTrimmedParityTraceV1
public import QuantitativeMaassTrimmedLVLowerV1
public import QuantitativeMaassLVParityLocalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

theorem windowParityOperatorTrace_trimmed_one_limit (N : ℕ) [NeZero N] (σ : ℝ) (hσ : σ^2=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t) (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0))
    (hRtop : Tendsto R atTop atTop) (hRδ : ∀ᶠ t in atTop,1/R t≤δ t)
    (hsmall : Tendsto (fun t => δ t/ε t) atTop (𝓝 0))
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => windowParityOperatorTrace N σ K he hc (R t)
      (hRp t) (t+δ t) (t+ε t-δ t) (Metric.closedBall o (R t)) 1/(t*ε t))
      atTop (𝓝 ((quotientMeasure N).real univ/(4*Real.pi))) := by
  obtain ⟨ι,hι,⟨B⟩⟩ := exists_countable_automorphic_basis N
  let : Countable ι := hι
  have hh := windowParity_local_trimmed_trace_main N B σ hσ K he hc hK hm o ε hε δ hδ R hRp hR1 hRlog hRtop hRδ hsmall hproduct
  apply hh.congr
  intro t
  rw [(windowParity_local_real_trace N B _ (isCompact_closedBall o (R t))
    σ hσ K he hc _ (hRp t) (t+δ t) (t+ε t-δ t)).tsum_eq,
    windowParityOperatorTrace_one]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (windowParityDensity_eq_canonical N σ hσ K he hc _
    (hRp t) (t+δ t) (t+ε t-δ t))

theorem actualLVFilter_parity_trimmed_eventual_lower (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (σ : ℝ) (hσ : σ^2=1) (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t) (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0))
    (hRtop : Tendsto R atTop atTop) (hRδ : ∀ᶠ t in atTop,1/R t≤δ t)
    (hsmall : Tendsto (fun t => δ t/ε t) atTop (𝓝 0))
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (d : ℕ) (hd : 0<d) (η : ℝ) (hη : 0<η) :
    ∀ᶠ t in atTop,(1/2-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-η<
      windowParityOperatorTrace N σ K he hc (R t) (hRp t)
        (t+δ t) (t+ε t-δ t) (Metric.closedBall o (R t))
        (actualLVFilter N p hN hpN a b hab d)/(t*ε t) := by
  have hl := actualLVFilter_window_trimmed_eventual_lower N p hN hpN hNp a b hab K he hc hK hm o ε hε δ hδ R hRp hR1 hRlog hRtop hRδ hsmall hproduct
    d hd (η/2) (by positivity)
  have hu := (windowParityOperatorTrace_trimmed_one_limit N (-σ) (by simpa only [neg_sq] using hσ)
    K he hc hK hm o ε hε δ hδ R hRp hR1 hRlog hRtop hRδ hsmall hproduct).eventually (gt_mem_nhds (lt_add_of_pos_right _ (by positivity : 0<η/2)))
  filter_upwards [hl,hu,hε,eventually_gt_atTop (0:ℝ)] with t hlt hut hεt htp
  have hb := div_le_div_of_nonneg_right
    (actualLVFilter_parity_integral_lower N p hN hpN hNp a b hab d σ hσ K he hc _
      (hRp t) (t+δ t) (t+ε t-δ t) _ (isCompact_closedBall o (R t)))
      (mul_pos htp hεt.1).le
  rw [sub_div] at hb
  have hcst : (1/2-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-η=
      ((1-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-η/2)-
      ((quotientMeasure N).real univ/(4*Real.pi)+η/2) := by ring
  rw [hcst]
  linarith only [hlt,hut,hb]


#print axioms windowParityOperatorTrace_trimmed_one_limit
#print axioms actualLVFilter_parity_trimmed_eventual_lower

end QuantitativeMaass
