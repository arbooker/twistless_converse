module

public import QuantitativeMaassLogPowerRadiusV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- The original triple-logarithmic resolution implies logarithmic resolution. -/
theorem width_mul_log_tendsto (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => ε t*Real.log t) atTop atTop := by
  have hsmall := (logPowerRadius_div_log (1/2) (by norm_num) (by norm_num)).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  apply tendsto_atTop_mono' _ _ hproduct
  filter_upwards [hε,slowScale_le_logPowerRadius_eventually (1/2) (by norm_num),hsmall,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t he hs hr ht
  have hh : logPowerRadius (1/2) t≤Real.log t := by
    have h := (div_lt_iff₀ ht).mp hr
    linarith
  exact mul_le_mul_of_nonneg_left (hs.trans hh) he.le

/-- Even the coarse entire exceptional bound is negligible for any propagation
radius o(log t), under the original admissible width hypothesis. -/
theorem exceptional_majorant_log_tendsto (ε R : ℝ → ℝ) (B C : ℝ)
    (hB : 0≤B) (hC : 0≤C) (hRp : ∀ᶠ t in atTop,0≤R t)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0)) :
    Tendsto (fun t => C*(R t)^2*Real.exp (B*R t)/(t*ε t)) atTop (𝓝 0) := by
  have hh := propagation_excess_tendsto Real.log ε R (B+2) 1 (by positivity) (by norm_num)
    Real.tendsto_log_atTop hε (width_mul_log_tendsto ε hε hproduct) hRlog
  have hmajor : Tendsto (fun t => C*(Real.exp ((B+2)*R t-Real.log t)/ε t)) atTop (𝓝 0) := by
    simpa only [one_mul,mul_zero] using hh.const_mul C
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    positivity
  · filter_upwards [hε,hRp,eventually_gt_atTop (0:ℝ)] with t he hr ht
    calc
      _ ≤ (C*Real.exp ((B+2)*R t))/(t*ε t) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (radius_square_exp_le B (R t) hr) hC
      _ = _ := by rw [Real.exp_sub,Real.exp_log ht]; ring

/-- The actual exceptional cusp spectral diagonal is o(t epsilon) at every
positive radius o(log t), for arbitrary intervals of length at most one. -/
theorem windowWavePacket_exceptional_flexible_negligible {ι : Type*}
    (N : ℕ) (hN : 0<N) (K : SchwartzMap ℝ ℝ) (hKe : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (ε R a b : ℝ → ℝ) (hRp : ∀ t,0<R t)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0))
    (hab : ∀ᶠ t in atTop,a t≤b t ∧ b t-a t≤1) :
    Tendsto (fun t =>
      (∑' i : {i // e i≤1/4},(inner ℂ (v i.val)
        ((windowWavePacket N K hc (R t) (hRp t) (a t) (b t)).comp
          (windowWavePacket N K hc (R t) (hRp t) (a t) (b t)) (v i.val))).re)/(t*ε t))
      atTop (𝓝 0) := by
  obtain ⟨B,C,hB,hC,hbound⟩ := windowWavePacket_exceptional_diagonal_bound N hN K hKe hc
  have hmajor := exceptional_majorant_log_tendsto ε R B C hB.le hC.le
    (Eventually.of_forall (fun t => (hRp t).le)) hε hproduct hRlog
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t het ht
    apply div_nonneg _ (mul_nonneg ht.le het.le)
    apply tsum_nonneg
    intro i
    rw [windowWavePacket_square_diagonal N K hKe hc]
    exact sq_nonneg _
  · filter_upwards [hε,hab,eventually_gt_atTop (0:ℝ)] with t het hw ht
    exact div_le_div_of_nonneg_right
      (hbound ι v hv hcusp e he hgraph _ (hRp t) _ _ hw.1 hw.2) (mul_nonneg ht.le het.le)

#print axioms width_mul_log_tendsto
#print axioms exceptional_majorant_log_tendsto
#print axioms windowWavePacket_exceptional_flexible_negligible

end QuantitativeMaass
