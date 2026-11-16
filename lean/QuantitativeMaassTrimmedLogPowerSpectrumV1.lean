module

public import QuantitativeMaassTrimmedLogPowerParityLVV1
public import QuantitativeMaassLVParityExistenceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- One fixed LV degree gives the full parity leading coefficient as a lower
bound for the genuine convergent cuspidal spectral sum. No spectral trace or
parity eigenbasis assumption is supplied. -/
theorem exists_windowParity_actualLV_trimmed_logPower_spectral_lower {κ : Type*}
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (δ : ℝ) (hδ : 0<δ) :
    ∃ d : ℕ,0<d ∧ ∀ (σ : ℝ),σ^2=1 → ∀ (K : SchwartzMap ℝ ℝ) (_he : Function.Even K)
      (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))),
      (∀ x,0≤K x) → (∫ x,K x)=1 → ∀ (_o : ℍ) (ε : ℝ → ℝ),
      (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
      Tendsto (fun t => ε t*slowScale t) atTop atTop →
      ∀ (c : ℝ),0<c → c<1 → ∀ᶠ t in atTop,(quotientMeasure N).real univ/(4*Real.pi)-δ<
        (∑' j,‖smoothPacketMultiplier (windowTimeSchwartz K hc (logPowerRadius c t)
          (logPowerRadius_pos c t) (t+logPowerMargin c t) (t+ε t-logPowerMargin c t)) (e j)‖^2 *
          (inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N σ (basis j:AutomorphicSpace N)))
            (parityProjection N σ (basis j:AutomorphicSpace N))).re)/(t*ε t) := by
  obtain ⟨d,hd,hbound⟩ := exists_actualLVFilter_parity_trimmed_logPower_eventual_lower N p hN hpN hNp a b hab δ hδ
  refine ⟨d,hd,?_⟩
  intro σ hσ K he hc hK hm o ε hε hproduct c hc0 hc1
  filter_upwards [hbound σ hσ K he hc hK hm o ε hε hproduct c hc0 hc1,hε,eventually_gt_atTop (0:ℝ)] with t ht hεt htp
  exact ht.trans_le (div_le_div_of_nonneg_right
    (windowParity_actualLV_trace_le_spectrum N p hN hpN hNp hpres a b hab d σ hσ basis e henergy hgraph
      K he hc _ (logPowerRadius_pos c t) (t+logPowerMargin c t) (t+ε t-logPowerMargin c t) _) (mul_pos htp hεt.1).le)

/-- A genuine countable cusp energy basis is constructed once. With this
basis one obtains the quantitative parity LV spectral lower bound for every
accuracy tolerance and every original admissible shrinking window. -/
theorem exists_constructed_parity_LV_trimmed_logPower_spectral_lower
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) :
    ∃ (κ : Type) (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ),
      Countable κ ∧ (∀ j,0≤e j) ∧
      (∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N))) ∧
      ∀ δ : ℝ,0<δ → ∃ d : ℕ,0<d ∧ ∀ (σ : ℝ),σ^2=1 →
      ∀ (K : SchwartzMap ℝ ℝ) (_he : Function.Even K)
        (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))),
        (∀ x,0≤K x) → (∫ x,K x)=1 → ∀ (_o : ℍ) (ε : ℝ → ℝ),
        (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
        Tendsto (fun t => ε t*slowScale t) atTop atTop →
        ∀ (c : ℝ),0<c → c<1 → ∀ᶠ t in atTop,(quotientMeasure N).real univ/(4*Real.pi)-δ<
          (∑' j,‖smoothPacketMultiplier (windowTimeSchwartz K hc (logPowerRadius c t)
            (logPowerRadius_pos c t) (t+logPowerMargin c t) (t+ε t-logPowerMargin c t)) (e j)‖^2 *
            (inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N σ (basis j:AutomorphicSpace N)))
              (parityProjection N σ (basis j:AutomorphicSpace N))).re)/(t*ε t) := by
  obtain ⟨κ,basis,e,henergy,hgraph,_⟩ := QuantitativeArithmeticMaassCuspBand.exists_cuspidal_energy_basis N hN
  refine ⟨κ,basis,e,cuspidal_basis_countable N hN basis,henergy,hgraph,?_⟩
  intro δ hδ
  exact exists_windowParity_actualLV_trimmed_logPower_spectral_lower N p hN hpN hNp hpres a b hab basis e henergy hgraph δ hδ


#print axioms exists_windowParity_actualLV_trimmed_logPower_spectral_lower
#print axioms exists_constructed_parity_LV_trimmed_logPower_spectral_lower

end QuantitativeMaass
