module

public import QuantitativeMaassMixedTraceLimitV1
public import QuantitativeMaassTrimmedMixedHeckeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- The actual full-volume mixed trace formula extends to every common finite
operator/symbol expansion, with the original shrinking-window hypotheses. -/
theorem mixedHeckeSpan_trimmed_trace_error (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t)
    (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0))
    (hRtop : Tendsto R atTop atTop)
    (hRδ : ∀ᶠ t in atTop,1/R t≤δ t)
    (hsmall : Tendsto (fun t => δ t/ε t) atTop (𝓝 0))
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    {v : HeckeWavePair N} (hv : v∈mixedHeckeSpan N p hN hpN a b hab) :
    Tendsto (fun t => (windowLocalOperatorTrace N K he hc (R t)
      (hRp t) (t+δ t) (t+ε t-δ t) (Metric.closedBall o (R t)) v.1-
      (quotientMeasure N).real univ*windowSymbolIdentity p K (R t) (t+δ t) (t+ε t-δ t) v.2)
      /(t*ε t)) atTop (𝓝 0) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨n,τ⟩,rfl⟩ := hv
    have hh := (actualMixedHecke_window_trimmed_trace_error τ N p hN hpN hNp a b hab K he hc o ε hε δ hδ R hRp hR1 hRlog n).add
      ((translatedWindowIdentity_trimmed_volume_error τ N K he hc hK hm o ε hε δ hδ R hRp hR1 hRtop hRδ hsmall hproduct).const_mul
        ((Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)))
    simp only [mul_zero,add_zero] at hh
    apply hh.congr'
    filter_upwards [hδ,eventually_gt_atTop (0:ℝ)] with t hd ht
    dsimp only [mixedHeckeSymbol]
    rw [windowSymbolIdentity_monomial p K he hc _ (hRp t) (t+δ t) (t+ε t-δ t) (by linarith [hd.1]) n τ]
    unfold windowLocalOperatorTrace
    change _=( (∫ x in Metric.closedBall o (R t),
      (inner ℂ (Wave.shiftedQuotientWave N τ (((HeckeL2.operator N p hN hpN a b hab)^n)
        (windowAbelColumn N K he hc (R t) (hRp t) (t+δ t) (t+ε t-δ t) x)))
      (windowAbelColumn N K he hc (R t) (hRp t) (t+δ t) (t+ε t-δ t) x)).re ∂quotientMeasure N)-_)/(t*ε t)
    ring
  | zero =>
    simp only [Prod.fst_zero,Prod.snd_zero,windowLocalOperatorTrace,zero_apply,
      inner_zero_left,Complex.zero_re,integral_zero,windowSymbolIdentity,finitePlaceSymbol,
      Pi.zero_apply,mul_zero,sub_zero,zero_div]
    exact tendsto_const_nhds
  | add u v hu hv ihu ihv =>
    have hh := ihu.add ihv
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards [hδ,eventually_gt_atTop (0:ℝ)] with t hd hp
    rw [Prod.fst_add,windowLocalOperatorTrace_add N K he hc _ (hRp t)
      (t+δ t) (t+ε t-δ t) _ (isCompact_closedBall o (R t)),
      windowSymbolIdentity_add N p hN hpN a b hab K hK hm _ (hRp t)
      (t+δ t) (t+ε t-δ t) (by linarith [hd.1]) (by linarith [hd.2]) hu hv]
    ring
  | smul c u hu ihu =>
    have hh := ihu.const_mul c
    rw [mul_zero] at hh
    apply hh.congr
    intro t
    change c*((windowLocalOperatorTrace N K he hc (R t)
      (hRp t) (t+δ t) (t+ε t-δ t) (Metric.closedBall o (R t)) u.1-
      (quotientMeasure N).real univ*windowSymbolIdentity p K (R t) (t+δ t) (t+ε t-δ t) u.2)/(t*ε t))=
      (windowLocalOperatorTrace N K he hc (R t)
      (hRp t) (t+δ t) (t+ε t-δ t) (Metric.closedBall o (R t)) (c • u.1)-
      (quotientMeasure N).real univ*windowSymbolIdentity p K (R t) (t+δ t) (t+ε t-δ t) (c • u.2))/(t*ε t)
    rw [windowLocalOperatorTrace_smul,windowSymbolIdentity_smul]
    ring

/-- The literal LV polynomial has its genuine finite-place/spherical trace
formula. The fixed degree is chosen before the spectral-window limit. -/
theorem actualLVFilter_window_trimmed_trace_error (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t)
    (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0))
    (hRtop : Tendsto R atTop atTop)
    (hRδ : ∀ᶠ t in atTop,1/R t≤δ t)
    (hsmall : Tendsto (fun t => δ t/ε t) atTop (𝓝 0))
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) (d : ℕ) :
    Tendsto (fun t => (windowLocalOperatorTrace N K he hc (R t)
      (hRp t) (t+δ t) (t+ε t-δ t) (Metric.closedBall o (R t))
      (actualLVFilter N p hN hpN a b hab d)-
      (quotientMeasure N).real univ*windowSymbolIdentity p K (R t) (t+δ t) (t+ε t-δ t)
        (fun z => 1-(1-(z.1-2*Real.cos (Real.log p*z.2))^2/(lvBound p)^2)^d))
      /(t*ε t)) atTop (𝓝 0) :=
by
  have hh := mixedHeckeSpan_trimmed_trace_error N p hN hpN hNp a b hab K he hc hK hm o ε hε δ hδ R hRp hR1 hRlog hRtop hRδ hsmall hproduct
    (v := (actualLVFilter N p hN hpN a b hab d,
      fun z : ℝ × ℝ => 1-(1-(z.1-2*Real.cos (Real.log p*z.2))^2/(lvBound p)^2)^d))
    (actualLVFilter_symbol_mem N p hN hpN a b hab d)
  exact hh

#print axioms mixedHeckeSpan_trimmed_trace_error
#print axioms actualLVFilter_window_trimmed_trace_error

end QuantitativeMaass
