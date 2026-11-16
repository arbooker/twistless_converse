module

public import QuantitativeMaassStrongLocalScaleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass.Strong

/-- Weighted decay at all sufficiently large centres gives one uniform
bound over a growing dyadic interval. No uniformity is inferred from a
limit with an additional uncontrolled parameter. -/
theorem weighted_decay_uniform_centres (g : ℝ → ℝ) (W : ℝ) (hW : 0≤W)
    (hg : Tendsto (fun t => Real.exp (W*strongScale t)*g t/t) atTop (𝓝 0)) :
    ∀ᶠ t in atTop,∀ s : ℝ,t/2≤s → s≤2*t →
      g s≤2*t*Real.exp (-(W/4)*strongScale t) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (hg.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)))
  filter_upwards [eventually_ge_atTop (2*T),eventually_gt_atTop (0:ℝ),
    strongScale_uniform_centres] with t ht ht0 hscale
  intro s hs hst
  have hs0 : 0<s := lt_of_lt_of_le (by positivity : 0<t/2) hs
  have hsT : T≤s := by linarith
  have hbound : Real.exp (W*strongScale s)*g s≤s := by
    have hh := (div_le_iff₀ hs0).mp (hT s hsT).le
    simpa only [one_mul] using hh
  have hg' : g s≤s*Real.exp (-(W*strongScale s)) := by
    have hh := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (-(W*strongScale s))).le
    have he : Real.exp (-(W*strongScale s))*(Real.exp (W*strongScale s)*g s)=g s := by
      rw [←mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
    rw [he] at hh
    simpa only [mul_comm] using hh
  have hexp : Real.exp (-(W*strongScale s))≤
      Real.exp (-(W/4)*strongScale t) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (hscale s hs) hW
    nlinarith only [hh]
  exact hg'.trans (mul_le_mul hst hexp (Real.exp_pos _).le (by positivity))

/-- The uniform centre bound can be summed over any finite cover whose
number of unit windows grows at a prescribed exponential rate. -/
theorem weighted_decay_finite_cover (g : ℝ → ℝ) (W K C : ℝ)
    (hW : 0≤W)
    (hg : Tendsto (fun t => Real.exp (W*strongScale t)*g t/t) atTop (𝓝 0)) :
    ∀ᶠ t in atTop,∀ {ι : Type*} [Fintype ι] (s : ι → ℝ),
      (∀ i,t/2≤s i ∧ s i≤2*t) →
      (Fintype.card ι:ℝ)≤C*Real.exp (K*strongScale t) →
      (∑ i,g (s i))≤2*C*t*Real.exp ((K-W/4)*strongScale t) := by
  filter_upwards [weighted_decay_uniform_centres g W hW hg,
    eventually_gt_atTop (0:ℝ)] with t ht ht0
  intro ι _ s hs hc
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => ht (s i) (hs i).1 (hs i).2)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have hcard := mul_le_mul_of_nonneg_right hc
    (show 0≤2*t*Real.exp (-(W/4)*strongScale t) by positivity)
  apply hh.trans (hcard.trans_eq _)
  calc
    _ = 2*C*t*(Real.exp (K*strongScale t)*Real.exp (-(W/4)*strongScale t)) := by ring
    _ = _ := by rw [←Real.exp_add]; congr 2; ring

#print axioms weighted_decay_uniform_centres
#print axioms weighted_decay_finite_cover

end QuantitativeMaass.Strong
