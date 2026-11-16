module

public import QuantitativeMaassWindowOperatorBoundsV1
public import QuantitativeMaassParametersV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped FourierTransform SchwartzMap Topology

namespace QuantitativeMaass

/-- Polynomial factors in a nonnegative time radius are absorbed in its exponential. -/
theorem radius_square_exp_le (B R : ℝ) (hR : 0≤R) :
    R^2*Real.exp (B*R) ≤ Real.exp ((B+2)*R) := by
  have hr : R≤Real.exp R := by linarith [Real.add_one_le_exp R]
  have hs := pow_le_pow_left₀ hR hr 2
  calc
    _ ≤ (Real.exp R)^2*Real.exp (B*R) :=
      mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
    _ = _ := by
      rw [pow_two,← Real.exp_add,← Real.exp_add]
      congr 1
      ring

/-- The triple-logarithmic scale has exponential much smaller than the spectral center. -/
theorem exp_slowScale_le_eventually : ∀ᶠ t : ℝ in atTop,Real.exp (slowScale t)≤t := by
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 1))] with t ht
  have htpos : 0<t := lt_of_lt_of_le (Real.exp_pos _) ht
  have hlog : Real.exp 1≤Real.log t := (Real.le_log_iff_exp_le htpos).mpr ht
  have hlogpos : 0<Real.log t := lt_of_lt_of_le (Real.exp_pos _) hlog
  have hloglog : 1≤Real.log (Real.log t) := (Real.le_log_iff_exp_le hlogpos).mpr hlog
  rw [slowScale,Real.exp_log (by linarith : 0<Real.log (Real.log t))]
  exact (Real.log_le_self hlogpos.le).trans (Real.log_le_self htpos.le)

/-- With any radius negligible relative to the slow scale, the entire
exceptional majorant is negligible relative to the shrinking-window main scale. -/
theorem exceptional_majorant_tendsto (ε R : ℝ → ℝ) (B C : ℝ)
    (hB : 0≤B) (hC : 0≤C) (hRpos : ∀ᶠ t in atTop,0≤R t)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hR : Tendsto (fun t => R t/slowScale t) atTop (𝓝 0)) :
    Tendsto (fun t => C*(R t)^2*Real.exp (B*R t)/(t*ε t)) atTop (𝓝 0) := by
  have hex := propagation_excess_tendsto slowScale ε R (B+2) 1
    (by linarith) (by norm_num) slowScale_tendsto hε hproduct hR
  have hmajor : Tendsto (fun t => C*(Real.exp ((B+2)*R t-slowScale t)/ε t)) atTop (𝓝 0) := by
    simpa only [mul_zero,one_mul] using hex.const_mul C
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    exact div_nonneg (mul_nonneg (mul_nonneg hC (sq_nonneg _)) (Real.exp_pos _).le)
      (mul_nonneg ht.le he.le)
  · filter_upwards [hε,hRpos,exp_slowScale_le_eventually] with t he hr ht
    have hden : 0<Real.exp (slowScale t)*ε t := mul_pos (Real.exp_pos _) he
    have hnum : 0≤C*(R t)^2*Real.exp (B*R t) :=
      mul_nonneg (mul_nonneg hC (sq_nonneg _)) (Real.exp_pos _).le
    calc
      _ ≤ (C*(R t)^2*Real.exp (B*R t))/(Real.exp (slowScale t)*ε t) :=
        div_le_div_of_nonneg_left hnum hden (mul_le_mul_of_nonneg_right ht he.le)
      _ ≤ (C*Real.exp ((B+2)*R t))/(Real.exp (slowScale t)*ε t) := by
        apply div_le_div_of_nonneg_right _ hden.le
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (radius_square_exp_le B (R t) hr) hC
      _ = _ := by rw [Real.exp_sub]; ring

/-- A globally positive version of the manuscript's radius, avoiding any
restriction on the width function at small spectral centers. -/
def positiveWindowRadius (ε : ℝ → ℝ) (t : ℝ) : ℝ :=
  max 1 (propagation (slowScale t) (ε t))

theorem positiveWindowRadius_pos (ε : ℝ → ℝ) (t : ℝ) : 0<positiveWindowRadius ε t :=
  lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)

theorem positiveWindowRadius_div_scale (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => positiveWindowRadius ε t/slowScale t) atTop (𝓝 0) := by
  have hinv : Tendsto (fun t => 1/slowScale t) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp slowScale_tendsto
  have hprop := (shrinking_window_parameters ε hε hproduct).1
  have hm := hinv.max hprop
  simp only [max_self] at hm
  apply hm.congr'
  filter_upwards [slowScale_tendsto.eventually (eventually_ge_atTop (0:ℝ))] with t ht
  exact max_div_div_right ht 1 (propagation (slowScale t) (ε t))

/-- The harmless global positivity convention agrees eventually with the
literal manuscript radius under its original width bound. -/
theorem positiveWindowRadius_eq_eventually (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1) :
    ∀ᶠ t in atTop,positiveWindowRadius ε t=propagation (slowScale t) (ε t) := by
  filter_upwards [hε,slowScale_tendsto.eventually (eventually_ge_atTop (1:ℝ))] with t he ht
  apply max_eq_right
  change 1≤Real.sqrt (slowScale t/ε t)
  apply Real.one_le_sqrt.mpr
  exact (le_div_iff₀ he.1).mpr (by linarith [he.2])

theorem positiveWindowRadius_resolves_width (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => positiveWindowRadius ε t*ε t) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ ((shrinking_window_parameters ε hε hproduct).2.1)
  filter_upwards [hε] with t ht
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le

/-- The actual exceptional positive diagonal is o(t epsilon), with the
radius constructed from the original width assumptions. No spectral estimate
or exceptional-finiteness premise is supplied by the caller. -/
theorem windowWavePacket_exceptional_diagonal_negligible {ι : Type*}
    (N : ℕ) (hN : 0<N) (K : SchwartzMap ℝ ℝ) (hKe : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (ε a b : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hab : ∀ᶠ t in atTop,a t≤b t ∧ b t-a t≤1) :
    Tendsto (fun t =>
      (∑' i : {i // e i≤1/4},(inner ℂ (v i.val)
        ((windowWavePacket N K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) (a t) (b t)).comp
          (windowWavePacket N K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) (a t) (b t))
          (v i.val))).re)/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨B,C,hB,hC,hbound⟩ := windowWavePacket_exceptional_diagonal_bound N hN K hKe hc
  have hmajor := exceptional_majorant_tendsto ε (positiveWindowRadius ε) B C hB.le hC.le
    (Eventually.of_forall (fun t => (positiveWindowRadius_pos ε t).le)) hε hproduct
    (positiveWindowRadius_div_scale ε hε hproduct)
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hpos
    apply div_nonneg _ (mul_nonneg hpos.le ht.le)
    apply tsum_nonneg
    intro i
    rw [windowWavePacket_square_diagonal N K hKe hc]
    exact sq_nonneg _
  · filter_upwards [hε,hab,eventually_gt_atTop (0:ℝ)] with t ht hw hpos
    exact div_le_div_of_nonneg_right
      (hbound ι v hv hcusp e he hgraph _ (positiveWindowRadius_pos ε t) _ _ hw.1 hw.2)
      (mul_nonneg hpos.le ht.le)

#print axioms positiveWindowRadius_eq_eventually
#print axioms positiveWindowRadius_resolves_width
#print axioms radius_square_exp_le
#print axioms exp_slowScale_le_eventually
#print axioms exceptional_majorant_tendsto
#print axioms positiveWindowRadius_pos
#print axioms positiveWindowRadius_div_scale
#print axioms windowWavePacket_exceptional_diagonal_negligible

end QuantitativeMaass
