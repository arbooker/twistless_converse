module

public import QuantitativeMaassLVParityComparisonV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- Actual localized trace with both Hilbert columns projected to one parity. -/
def windowParityOperatorTrace (N : ℕ) [NeZero N] (σ : ℝ)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (S : Set ℍ) (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) : ℝ :=
  ∫ x in S,(inner ℂ (A (parityProjection N σ (windowAbelColumn N K he hc R hR a b x)))
    (parityProjection N σ (windowAbelColumn N K he hc R hR a b x))).re ∂quotientMeasure N

theorem windowParityOperatorTrace_integrable (N : ℕ) [NeZero N] (σ : ℝ)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (S : Set ℍ) (hS : IsCompact S)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    IntegrableOn (fun x => (inner ℂ (A (parityProjection N σ (windowAbelColumn N K he hc R hR a b x)))
      (parityProjection N σ (windowAbelColumn N K he hc R hR a b x))).re) S (quotientMeasure N) := by
  have hcol := (parityProjection N σ).continuous.comp (windowAbelColumn_continuous N K he hc R hR a b)
  exact (Complex.continuous_re.comp ((A.continuous.comp hcol).inner hcol)).continuousOn.integrableOn_compact hS

/-- The unfiltered parity trace is exactly its projected-column norm integral. -/
theorem windowParityOperatorTrace_one (N : ℕ) [NeZero N] (σ : ℝ)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (S : Set ℍ) :
    windowParityOperatorTrace N σ K he hc R hR a b S 1=
      ∫ x in S,‖parityProjection N σ (windowAbelColumn N K he hc R hR a b x)‖^2 ∂quotientMeasure N := by
  unfold windowParityOperatorTrace
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [one_apply_eq_self]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (parityProjection N σ (windowAbelColumn N K he hc R hR a b x)))

/-- Canonical window columns realize the previously computed positive parity density. -/
theorem windowParityDensity_eq_canonical (N : ℕ) [NeZero N] (σ : ℝ) (hσ : σ^2=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (x : ℍ) :
    windowParityDensity N σ K hc R hR a b x=
      ‖parityProjection N σ (windowAbelColumn N K he hc R hR a b x)‖^2 := by
  unfold windowAbelColumn
  exact windowParityDensity_eq_column N σ hσ K he hc R hR a b _ _ _ x

/-- The unfiltered parity trace has its main term without a supplied Hilbert
basis; a countable full-space basis is constructed internally. -/
theorem windowParityOperatorTrace_one_limit (N : ℕ) [NeZero N] (σ : ℝ) (hσ : σ^2=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => windowParityOperatorTrace N σ K he hc (positiveWindowRadius ε t)
      (positiveWindowRadius_pos ε t) t (t+ε t) (Metric.closedBall o (positiveWindowRadius ε t)) 1/(t*ε t))
      atTop (𝓝 ((quotientMeasure N).real univ/(4*Real.pi))) := by
  obtain ⟨ι,hι,⟨B⟩⟩ := exists_countable_automorphic_basis N
  let : Countable ι := hι
  have hh := windowParity_local_trace_main N B σ hσ K he hc hK hm o ε hε hproduct
  apply hh.congr
  intro t
  rw [(windowParity_local_real_trace N B _ (isCompact_closedBall o (positiveWindowRadius ε t))
    σ hσ K he hc _ (positiveWindowRadius_pos ε t) t (t+ε t)).tsum_eq,
    windowParityOperatorTrace_one]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (windowParityDensity_eq_canonical N σ hσ K he hc _
    (positiveWindowRadius_pos ε t) t (t+ε t))

/-- Integrated opposite-parity subtraction on every compact localization. -/
theorem actualLVFilter_parity_integral_lower (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ) (σ : ℝ) (hσ : σ^2=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (u v : ℝ) (S : Set ℍ) (hS : IsCompact S) :
    windowLocalOperatorTrace N K he hc R hR u v S (actualLVFilter N p hN hpN a b hab d)-
      windowParityOperatorTrace N (-σ) K he hc R hR u v S 1≤
    windowParityOperatorTrace N σ K he hc R hR u v S (actualLVFilter N p hN hpN a b hab d) := by
  let A := actualLVFilter N p hN hpN a b hab d
  have hi := windowLocalOperatorTrace_integrable N K he hc R hR u v S hS A
  have hj : IntegrableOn (fun x => ‖parityProjection N (-σ) (windowAbelColumn N K he hc R hR u v x)‖^2)
      S (quotientMeasure N) :=
    (((parityProjection N (-σ)).continuous.comp (windowAbelColumn_continuous N K he hc R hR u v)).norm.pow 2).continuousOn.integrableOn_compact hS
  have hk := windowParityOperatorTrace_integrable N σ K he hc R hR u v S hS A
  rw [windowParityOperatorTrace_one]
  unfold windowLocalOperatorTrace windowParityOperatorTrace
  rw [← integral_sub hi hj]
  apply integral_mono (hi.sub hj) hk
  intro x
  exact actualLVFilter_parity_lower N p hN hpN hNp a b hab d σ hσ _

/-- Actual fixed-parity LV trace lower bound with its explicit degree deficit.
Only the checked unfiltered parity geometry is used. -/
theorem actualLVFilter_parity_eventual_lower (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (σ : ℝ) (hσ : σ^2=1) (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (d : ℕ) (hd : 0<d) (η : ℝ) (hη : 0<η) :
    ∀ᶠ t in atTop,(1/2-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-η<
      windowParityOperatorTrace N σ K he hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
        t (t+ε t) (Metric.closedBall o (positiveWindowRadius ε t))
        (actualLVFilter N p hN hpN a b hab d)/(t*ε t) := by
  have hl := actualLVFilter_window_eventual_lower N p hN hpN hNp a b hab K he hc hK hm o ε hε hproduct
    d hd (η/2) (by positivity)
  have hu := (windowParityOperatorTrace_one_limit N (-σ) (by simpa only [neg_sq] using hσ)
    K he hc hK hm o ε hε hproduct).eventually (gt_mem_nhds (lt_add_of_pos_right _ (by positivity : 0<η/2)))
  filter_upwards [hl,hu,hε,eventually_gt_atTop (0:ℝ)] with t hlt hut hεt htp
  have hb := div_le_div_of_nonneg_right
    (actualLVFilter_parity_integral_lower N p hN hpN hNp a b hab d σ hσ K he hc _
      (positiveWindowRadius_pos ε t) t (t+ε t) _ (isCompact_closedBall o (positiveWindowRadius ε t)))
      (mul_pos htp hεt.1).le
  rw [sub_div] at hb
  have hcst : (1/2-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-η=
      ((1-lvSphericalDeficit p d)*(quotientMeasure N).real univ/(2*Real.pi)-η/2)-
      ((quotientMeasure N).real univ/(4*Real.pi)+η/2) := by ring
  rw [hcst]
  linarith only [hlt,hut,hb]

#print axioms windowParityOperatorTrace_integrable
#print axioms windowParityOperatorTrace_one
#print axioms windowParityDensity_eq_canonical
#print axioms windowParityOperatorTrace_one_limit
#print axioms actualLVFilter_parity_integral_lower
#print axioms actualLVFilter_parity_eventual_lower

end QuantitativeMaass
