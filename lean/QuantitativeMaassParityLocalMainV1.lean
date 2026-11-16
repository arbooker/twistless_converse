module

public import QuantitativeMaassWindowIdentityLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- The actual prescribed propagation radius tends to infinity under the
original shrinking-window assumptions. -/
theorem positiveWindowRadius_tendsto_atTop (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (positiveWindowRadius ε) atTop atTop := by
  apply tendsto_atTop_mono' atTop _
    (positiveWindowRadius_resolves_width ε (hε.mono (fun _ h => h.1)) hproduct)
  filter_upwards [hε] with t ht
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 (positiveWindowRadius_pos ε t).le

/-- Expanding centre balls exhaust the finite actual quotient measure. -/
theorem quotientMeasure_expanding_ball_limit (N : ℕ) [NeZero N] (o : ℍ)
    (R : ℝ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun t => (quotientMeasure N).real (Metric.closedBall o (R t)))
      atTop (𝓝 ((quotientMeasure N).real univ)) := by
  have hm : Monotone (fun r : ℝ => Metric.closedBall o r) :=
    fun _ _ h => Metric.closedBall_subset_closedBall h
  have hu : (⋃ r : ℝ,Metric.closedBall o r)=univ := by
    ext x
    simp only [mem_iUnion,Metric.mem_closedBall,mem_univ,iff_true]
    exact ⟨dist x o,le_rfl⟩
  have hh := tendsto_measure_iUnion_atTop (μ := quotientMeasure N) hm
  rw [hu] at hh
  exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp (hh.comp hR)

/-- The actual full-quotient parity trace, localized on the prescribed expanding
balls and formed from the original literal moving-window operator, has its
leading coefficient. This statement is about a local Hilbert trace, not yet
about the cuspidal eigenvalue counting function. -/
theorem windowParity_local_trace_main {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (σ : ℝ) (hσ : σ^2=1) (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      (∑' i,∫ x in Metric.closedBall o (positiveWindowRadius ε t),
        ‖(windowWavePacket N K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
          t (t+ε t) (parityProjection N σ (b i))).val x‖^2 ∂quotientMeasure N)/(t*ε t))
      atTop (𝓝 ((quotientMeasure N).real univ/(4*Real.pi))) := by
  let A := fun t => ∑' i,∫ x in Metric.closedBall o (positiveWindowRadius ε t),
    ‖(windowWavePacket N K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
      t (t+ε t) (parityProjection N σ (b i))).val x‖^2 ∂quotientMeasure N
  let V := fun t => (quotientMeasure N).real (Metric.closedBall o (positiveWindowRadius ε t))
  let I := fun t => (windowIdentityContribution K hc (positiveWindowRadius ε t)
    (positiveWindowRadius_pos ε t) t (t+ε t)).re
  have hgeom := windowParity_local_trace_geometric_negligible N b σ hσ K he hc o ε hε hproduct
  have herr : Tendsto (fun t => A t/(t*ε t)-V t*(I t/(t*ε t))/2) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply hgeom.congr'
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hp
    change |A t-V t*I t/2|/(t*ε t)=‖A t/(t*ε t)-V t*(I t/(t*ε t))/2-0‖
    rw [sub_zero,show A t/(t*ε t)-V t*(I t/(t*ε t))/2=(A t-V t*I t/2)/(t*ε t) by ring,
      Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos hp ht.1)]
  have hV := quotientMeasure_expanding_ball_limit N o (positiveWindowRadius ε)
    (positiveWindowRadius_tendsto_atTop ε hε hproduct)
  have hI := windowIdentityContribution_interval_normalized K he hc hK hm ε hε hproduct
  have hmain := (hV.mul hI).div_const 2
  change Tendsto (fun t => V t*(I t/(t*ε t))/2) atTop
    (𝓝 ((quotientMeasure N).real univ*(1/(2*Real.pi))/2)) at hmain
  have hh := herr.add hmain
  simp only [sub_add_cancel,zero_add] at hh
  convert hh using 1
  ring

#print axioms positiveWindowRadius_tendsto_atTop
#print axioms quotientMeasure_expanding_ball_limit
#print axioms windowParity_local_trace_main

end QuantitativeMaass
