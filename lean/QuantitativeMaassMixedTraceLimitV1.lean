module

public import QuantitativeMaassMixedTraceLinearV1

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
theorem mixedHeckeSpan_trace_error (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    {v : HeckeWavePair N} (hv : v∈mixedHeckeSpan N p hN hpN a b hab) :
    Tendsto (fun t => (windowLocalOperatorTrace N K he hc (positiveWindowRadius ε t)
      (positiveWindowRadius_pos ε t) t (t+ε t) (Metric.closedBall o (positiveWindowRadius ε t)) v.1-
      (quotientMeasure N).real univ*windowSymbolIdentity p K (positiveWindowRadius ε t) t (t+ε t) v.2)
      /(t*ε t)) atTop (𝓝 0) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨n,τ⟩,rfl⟩ := hv
    have hh := (actualMixedHecke_window_trace_error τ N p hN hpN hNp a b hab K he hc o ε hε hproduct n).add
      ((translatedWindowIdentity_volume_error τ N K he hc hK hm o ε hε hproduct).const_mul
        ((Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)))
    simp only [mul_zero,add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    dsimp only [mixedHeckeSymbol]
    rw [windowSymbolIdentity_monomial p K he hc _ (positiveWindowRadius_pos ε t) t (t+ε t) ht n τ]
    unfold windowLocalOperatorTrace
    change _=( (∫ x in Metric.closedBall o (positiveWindowRadius ε t),
      (inner ℂ (Wave.shiftedQuotientWave N τ (((HeckeL2.operator N p hN hpN a b hab)^n)
        (windowAbelColumn N K he hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) t (t+ε t) x)))
      (windowAbelColumn N K he hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) t (t+ε t) x)).re ∂quotientMeasure N)-_)/(t*ε t)
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
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hp
    rw [Prod.fst_add,windowLocalOperatorTrace_add N K he hc _ (positiveWindowRadius_pos ε t)
      t (t+ε t) _ (isCompact_closedBall o (positiveWindowRadius ε t)),
      windowSymbolIdentity_add N p hN hpN a b hab K hK hm _ (positiveWindowRadius_pos ε t)
      t (t+ε t) hp (le_add_of_nonneg_right ht.1.le) hu hv]
    ring
  | smul c u hu ihu =>
    have hh := ihu.const_mul c
    rw [mul_zero] at hh
    apply hh.congr
    intro t
    change c*((windowLocalOperatorTrace N K he hc (positiveWindowRadius ε t)
      (positiveWindowRadius_pos ε t) t (t+ε t) (Metric.closedBall o (positiveWindowRadius ε t)) u.1-
      (quotientMeasure N).real univ*windowSymbolIdentity p K (positiveWindowRadius ε t) t (t+ε t) u.2)/(t*ε t))=
      (windowLocalOperatorTrace N K he hc (positiveWindowRadius ε t)
      (positiveWindowRadius_pos ε t) t (t+ε t) (Metric.closedBall o (positiveWindowRadius ε t)) (c • u.1)-
      (quotientMeasure N).real univ*windowSymbolIdentity p K (positiveWindowRadius ε t) t (t+ε t) (c • u.2))/(t*ε t)
    rw [windowLocalOperatorTrace_smul,windowSymbolIdentity_smul]
    ring

/-- The literal LV polynomial has its genuine finite-place/spherical trace
formula. The fixed degree is chosen before the spectral-window limit. -/
theorem actualLVFilter_window_trace_error (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) (d : ℕ) :
    Tendsto (fun t => (windowLocalOperatorTrace N K he hc (positiveWindowRadius ε t)
      (positiveWindowRadius_pos ε t) t (t+ε t) (Metric.closedBall o (positiveWindowRadius ε t))
      (actualLVFilter N p hN hpN a b hab d)-
      (quotientMeasure N).real univ*windowSymbolIdentity p K (positiveWindowRadius ε t) t (t+ε t)
        (fun z => 1-(1-(z.1-2*Real.cos (Real.log p*z.2))^2/(lvBound p)^2)^d))
      /(t*ε t)) atTop (𝓝 0) :=
by
  have hh := mixedHeckeSpan_trace_error N p hN hpN hNp a b hab K he hc hK hm o ε hε hproduct
    (v := (actualLVFilter N p hN hpN a b hab d,
      fun z : ℝ × ℝ => 1-(1-(z.1-2*Real.cos (Real.log p*z.2))^2/(lvBound p)^2)^d))
    (actualLVFilter_symbol_mem N p hN hpN a b hab d)
  exact hh

#print axioms mixedHeckeSpan_trace_error
#print axioms actualLVFilter_window_trace_error

end QuantitativeMaass
