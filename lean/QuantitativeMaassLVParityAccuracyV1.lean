module

public import QuantitativeMaassLVParityLocalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- The explicit finite-place deficit tends to zero with the fixed filter degree. -/
theorem lvSphericalDeficit_tendsto (p : ℕ) :
    Tendsto (fun d : ℕ => lvSphericalDeficit p d) atTop (𝓝 0) := by
  have hn : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hh := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hn)).const_mul
    (unramifiedDensityBound (p:ℝ)*lvBound p*Real.sqrt Real.pi)
  simpa only [lvSphericalDeficit,div_eq_mul_inv,mul_zero,Function.comp_apply] using hh

/-- A positive degree can be chosen from the level-volume and tolerance before
any window, parity, spectral centre or smoothing kernel is chosen. -/
theorem exists_lvSphericalDeficit_degree (p : ℕ) (V δ : ℝ) (hδ : 0<δ) :
    ∃ d : ℕ,0<d ∧ lvSphericalDeficit p d*V/(2*Real.pi)<δ := by
  have hh := ((lvSphericalDeficit_tendsto p).mul_const V).div_const (2*Real.pi)
  simp only [zero_mul,zero_div] at hh
  obtain ⟨d,hd,he⟩ := ((eventually_ge_atTop (1:ℕ)).and (hh.eventually (gt_mem_nhds hδ))).exists
  exact ⟨d,by omega,he⟩

/-- For every accuracy tolerance, one fixed genuine LV filter attains the full
parity coefficient asymptotically under the original width assumptions. -/
theorem exists_actualLVFilter_parity_eventual_lower (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (δ : ℝ) (hδ : 0<δ) :
    ∃ d : ℕ,0<d ∧ ∀ (σ : ℝ),σ^2=1 → ∀ (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
      (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))),
      (∀ x,0≤K x) → (∫ x,K x)=1 → ∀ (o : ℍ) (ε : ℝ → ℝ),
      (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
      Tendsto (fun t => ε t*slowScale t) atTop atTop →
      ∀ᶠ t in atTop,(quotientMeasure N).real univ/(4*Real.pi)-δ<
        windowParityOperatorTrace N σ K he hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
          t (t+ε t) (Metric.closedBall o (positiveWindowRadius ε t))
          (actualLVFilter N p hN hpN a b hab d)/(t*ε t) := by
  obtain ⟨d,hd,hdef⟩ := exists_lvSphericalDeficit_degree p ((quotientMeasure N).real univ) (δ/2) (by positivity)
  refine ⟨d,hd,?_⟩
  intro σ hσ K he hc hK hm o ε hε hproduct
  have hh := actualLVFilter_parity_eventual_lower N p hN hpN hNp a b hab σ hσ K he hc hK hm o ε hε hproduct
    d hd (δ/2) (by positivity)
  have hb : (quotientMeasure N).real univ/(4*Real.pi)-δ<
      (1/2-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-δ/2 := by
    rw [show (1/2-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-δ/2=
      (quotientMeasure N).real univ/(4*Real.pi)-lvSphericalDeficit p d*(quotientMeasure N).real univ/(2*Real.pi)-δ/2 by ring]
    linarith only [hdef]
  exact hh.mono (fun _ ht => hb.trans ht)

#print axioms lvSphericalDeficit_tendsto
#print axioms exists_lvSphericalDeficit_degree
#print axioms exists_actualLVFilter_parity_eventual_lower

end QuantitativeMaass
