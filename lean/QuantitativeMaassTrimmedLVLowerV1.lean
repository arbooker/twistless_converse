module

public import QuantitativeMaassLVGeometricLowerV1
public import QuantitativeMaassTrimmedLVTraceV1
public import QuantitativeMaassLogPowerRadiusV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- A genuine quantitative LV lower estimate for the actual full quotient
local trace, with degree fixed before the spectral limit. Parity and sharp
cuspidal counting are separate steps. -/
theorem actualLVFilter_window_trimmed_eventual_lower (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
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
    ∀ᶠ t in atTop,(1-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-η<
      windowLocalOperatorTrace N K he hc (R t) (hRp t)
        (t+δ t) (t+ε t-δ t) (Metric.closedBall o (R t))
        (actualLVFilter N p hN hpN a b hab d)/(t*ε t) := by
  have herror := actualLVFilter_window_trimmed_trace_error N p hN hpN hNp a b hab K he hc hK hm o ε hε δ hδ R hRp hR1 hRlog hRtop hRδ hsmall hproduct d
  have hi := (windowIdentityContribution_trimmed_normalized K he hc hK hm ε hε δ hδ R hRp hR1 hRδ hsmall hproduct).const_mul
    ((quotientMeasure N).real univ*(1-lvSphericalDeficit p d))
  have hlim := herror.add hi
  simp only [zero_add] at hlim
  have hnear := hlim.eventually (lt_mem_nhds (by
    change (1-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-η<
      (quotientMeasure N).real univ*(1-lvSphericalDeficit p d)*(1/(2*Real.pi))
    rw [show (quotientMeasure N).real univ*(1-lvSphericalDeficit p d)*(1/(2*Real.pi))=
      (1-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi) by ring]
    exact sub_lt_self _ hη))
  filter_upwards [hnear,hε,hδ,eventually_gt_atTop (0:ℝ)] with t ht hεt hdelt htp
  apply lt_of_lt_of_le ht
  have hb := (windowSymbolIdentity_actualLV_bounds N p hN hpN a b hab K
    he hc hK hm _ (hRp t)
    (t+δ t) (t+ε t-δ t) (by linarith [hdelt.1]) (by linarith [hdelt.2]) d hd).1
  have hv : 0≤(quotientMeasure N).real univ := measureReal_nonneg
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hv) (mul_pos htp hεt.1).le
  have numeric (X Y Z V D q : ℝ) (h : V*((1-D)*Z)/q≤V*Y/q) :
      (X-V*Y)/q+V*(1-D)*(Z/q)≤X/q := by
    ring_nf at h ⊢
    linarith only [h]
  exact numeric _ _ _ _ _ _ hh

#print axioms actualLVFilter_window_trimmed_eventual_lower

end QuantitativeMaass
