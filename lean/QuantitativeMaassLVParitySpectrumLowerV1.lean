module

public import QuantitativeMaassLVParityCuspTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- A compactly localized actual parity LV trace is bounded by its ordinary
cuspidal spectral sum, including exceptional energies. -/
theorem windowParity_actualLV_trace_le_spectrum {κ : Type*}
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ) (σ : ℝ) (hσ : σ^2=1)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (u v : ℝ) (S : Set ℍ) :
    windowParityOperatorTrace N σ K he hc R hR u v S (actualLVFilter N p hN hpN a b hab d)≤
      ∑' j,‖smoothPacketMultiplier (windowTimeSchwartz K hc R hR u v) (e j)‖^2 *
        (inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N σ (basis j:AutomorphicSpace N)))
          (parityProjection N σ (basis j:AutomorphicSpace N))).re := by
  let B := (symmetricWindowTimeTest_uniform_support K hc).choose
  have hB := (symmetricWindowTimeTest_uniform_support K hc).choose_spec.1
  have hs := (symmetricWindowTimeTest_uniform_support K hc).choose_spec.2
  let f := windowTimeSchwartz K hc R hR u v
  have hfc : HasCompactSupport (f : ℝ → ℂ) := symmetricWindowTimeTest_compact K hc R u v hR
  have hfe : Function.Even f := symmetricWindowTimeTest_even K he R u v
  have hfr : ∀ t,star (f t)=f t := symmetricWindowTimeTest_real K he R u v
  have hint := timeWavePacket_parity_actualLV_kernel_integrable N p hN hpN hNp hpres a b hab d σ hσ
    f hfc hfe hfr (B*R) (mul_nonneg hB.le hR.le) (hs R hR u v)
  have hsum := timeWavePacket_parity_actualLV_real_trace N p hN hpN hNp hpres a b hab d σ hσ
    basis e henergy hgraph f hfc hfe hfr (B*R) (mul_nonneg hB.le hR.le) (hs R hR u v)
  rw [hsum.tsum_eq]
  unfold windowParityOperatorTrace windowAbelColumn
  exact setIntegral_le_integral hint (Eventually.of_forall (fun x =>
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (actualLVFilter_order N p hN hpN a b hab d).1).re_inner_nonneg_left _))

/-- One fixed LV degree gives the full parity leading coefficient as a lower
bound for the genuine convergent cuspidal spectral sum. No spectral trace or
parity eigenbasis assumption is supplied. -/
theorem exists_windowParity_actualLV_spectral_lower {κ : Type*}
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
      ∀ᶠ t in atTop,(quotientMeasure N).real univ/(4*Real.pi)-δ<
        (∑' j,‖smoothPacketMultiplier (windowTimeSchwartz K hc (positiveWindowRadius ε t)
          (positiveWindowRadius_pos ε t) t (t+ε t)) (e j)‖^2 *
          (inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N σ (basis j:AutomorphicSpace N)))
            (parityProjection N σ (basis j:AutomorphicSpace N))).re)/(t*ε t) := by
  obtain ⟨d,hd,hbound⟩ := exists_actualLVFilter_parity_eventual_lower N p hN hpN hNp a b hab δ hδ
  refine ⟨d,hd,?_⟩
  intro σ hσ K he hc hK hm o ε hε hproduct
  filter_upwards [hbound σ hσ K he hc hK hm o ε hε hproduct,hε,eventually_gt_atTop (0:ℝ)] with t ht hεt htp
  exact ht.trans_le (div_le_div_of_nonneg_right
    (windowParity_actualLV_trace_le_spectrum N p hN hpN hNp hpres a b hab d σ hσ basis e henergy hgraph
      K he hc _ (positiveWindowRadius_pos ε t) t (t+ε t) _) (mul_pos htp hεt.1).le)

#print axioms windowParity_actualLV_trace_le_spectrum
#print axioms exists_windowParity_actualLV_spectral_lower

end QuantitativeMaass
