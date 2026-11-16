module

public import QuantitativeMaassTrimmedParityLVV1
public import QuantitativeMaassLVParityAccuracyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

theorem actualLVFilter_parity_trimmed_logPower_eventual_lower (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (σ : ℝ) (hσ : σ^2=1) (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (c : ℝ) (hc0 : 0<c) (hc1 : c<1)
    (d : ℕ) (hd : 0<d) (η : ℝ) (hη : 0<η) :
    ∀ᶠ t in atTop,(1/2-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-η<
      windowParityOperatorTrace N σ K he hc (logPowerRadius c t) (logPowerRadius_pos c t)
        (t+logPowerMargin c t) (t+ε t-logPowerMargin c t) (Metric.closedBall o (logPowerRadius c t))
        (actualLVFilter N p hN hpN a b hab d)/(t*ε t) := by
  exact actualLVFilter_parity_trimmed_eventual_lower N p hN hpN hNp a b hab σ hσ K he hc hK hm o ε hε
    (logPowerMargin c) (logPowerMargin_trim_parameters c hc0 ε (hε.mono (fun _ h => h.1)) hproduct).1
    (logPowerRadius c) (logPowerRadius_pos c) (Eventually.of_forall (fun _ => le_max_left _ _))
    (logPowerRadius_div_log c hc0 hc1) (logPowerRadius_tendsto c hc0)
    (Eventually.of_forall (logPowerMargin_trim_parameters c hc0 ε (hε.mono (fun _ h => h.1)) hproduct).2)
    (logPowerMargin_div_width c hc0 ε (hε.mono (fun _ h => h.1)) hproduct) hproduct d hd η hη

/-- For every accuracy tolerance, one fixed genuine LV filter attains the full
parity coefficient asymptotically under the original width assumptions. -/
theorem exists_actualLVFilter_parity_trimmed_logPower_eventual_lower (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (δ : ℝ) (hδ : 0<δ) :
    ∃ d : ℕ,0<d ∧ ∀ (σ : ℝ),σ^2=1 → ∀ (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
      (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))),
      (∀ x,0≤K x) → (∫ x,K x)=1 → ∀ (o : ℍ) (ε : ℝ → ℝ),
      (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
      Tendsto (fun t => ε t*slowScale t) atTop atTop →
      ∀ (c : ℝ),0<c → c<1 → ∀ᶠ t in atTop,(quotientMeasure N).real univ/(4*Real.pi)-δ<
        windowParityOperatorTrace N σ K he hc (logPowerRadius c t) (logPowerRadius_pos c t)
          (t+logPowerMargin c t) (t+ε t-logPowerMargin c t) (Metric.closedBall o (logPowerRadius c t))
          (actualLVFilter N p hN hpN a b hab d)/(t*ε t) := by
  obtain ⟨d,hd,hdef⟩ := exists_lvSphericalDeficit_degree p ((quotientMeasure N).real univ) (δ/2) (by positivity)
  refine ⟨d,hd,?_⟩
  intro σ hσ K he hc hK hm o ε hε hproduct c hc0 hc1
  have hh := actualLVFilter_parity_trimmed_logPower_eventual_lower N p hN hpN hNp a b hab σ hσ K he hc hK hm o ε hε hproduct c hc0 hc1
    d hd (δ/2) (by positivity)
  have hb : (quotientMeasure N).real univ/(4*Real.pi)-δ<
      (1/2-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-δ/2 := by
    rw [show (1/2-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-δ/2=
      (quotientMeasure N).real univ/(4*Real.pi)-lvSphericalDeficit p d*(quotientMeasure N).real univ/(2*Real.pi)-δ/2 by ring]
    linarith only [hdef]
  exact hh.mono (fun _ ht => hb.trans ht)


#print axioms actualLVFilter_parity_trimmed_logPower_eventual_lower
#print axioms exists_actualLVFilter_parity_trimmed_logPower_eventual_lower

end QuantitativeMaass
