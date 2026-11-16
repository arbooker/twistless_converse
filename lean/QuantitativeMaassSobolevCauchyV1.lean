module

public import QuantitativeMaassPoincareCoordinateBoundV1
public import QuantitativeMaassWeightedSeedSobolevV1
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantitativeMaass

/-- A compact Lipschitz seed has an actual square-integrable derivative. -/
theorem lipschitz_fderiv_memLp {K : NNReal} {f : (ℝ×ℝ) → ℂ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) :
    MemLp (fderiv ℝ f) 2 volume := by
  have hm := (measurable_fderiv ℝ f).aestronglyMeasurable (μ := volume)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hs : Function.support (fun x => ‖fderiv ℝ f x‖^2)⊆tsupport f := by
    intro x hx
    by_contra hn
    exact hx (by simp only [fderiv_of_notMem_tsupport ℝ hn,norm_zero,zero_pow (by decide : 2≠0)])
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply (integrableOn_const (C := (K:ℝ)^2) hc.isCompact.measure_ne_top).mono'
    ((measurable_fderiv ℝ f).norm.pow_const 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hf) 2

/-- Square-integral errors about a common limit bound pairwise errors. -/
theorem integral_sub_square_le {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure A} {f g h : A → E} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) :
    (∫ x,‖f x-g x‖^2 ∂μ)≤2*(∫ x,‖f x-h x‖^2 ∂μ)+2*(∫ x,‖g x-h x‖^2 ∂μ) := by
  have h1 : Integrable (fun x => ‖f x-h x‖^2) μ := by
    simpa only [Pi.sub_apply] using (hf.sub hh).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have h2 : Integrable (fun x => ‖g x-h x‖^2) μ := by
    simpa only [Pi.sub_apply] using (hg.sub hh).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hb (x : A) : ‖f x-g x‖^2≤2*‖f x-h x‖^2+2*‖g x-h x‖^2 := by
    have ht : ‖f x-g x‖≤‖f x-h x‖+‖g x-h x‖ := by
      simpa only [sub_sub_sub_cancel_right] using norm_sub_le (f x-h x) (g x-h x)
    have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
    nlinarith [sq_nonneg (‖f x-h x‖-‖g x-h x‖)]
  have hi := integral_mono_of_nonneg (Eventually.of_forall (fun x => sq_nonneg ‖f x-g x‖))
    ((h1.const_mul 2).add (h2.const_mul 2)) (Eventually.of_forall hb)
  simp only [Pi.add_apply] at hi
  rw [integral_add (h1.const_mul 2) (h2.const_mul 2),integral_const_mul,integral_const_mul] at hi
  exact hi

/-- Quantitative squared-distance errors give a genuine Cauchy sequence. -/
theorem cauchySeq_of_norm_sub_square_le {E : Type*} [NormedAddCommGroup E]
    {u : ℕ → E} {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ m n,‖u m-u n‖^2≤e m+e n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp he).2 (ε^2/2) (by positivity))
  refine ⟨N,?_⟩
  intro m hm n hn
  rw [dist_eq_norm]
  have h1 := hN m hm
  have h2 := hN n hn
  have h3 := hb m n
  nlinarith [norm_nonneg (u m-u n)]

#print axioms lipschitz_fderiv_memLp
#print axioms integral_sub_square_le
#print axioms cauchySeq_of_norm_sub_square_le

end QuantitativeMaass
