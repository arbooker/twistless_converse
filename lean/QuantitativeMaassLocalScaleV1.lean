module

public import QuantitativeMaassWeightedWidthDecayV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass

theorem log_half_lower {x : ℝ} (hx : 0<x) (hl : 2*Real.log 2≤Real.log x) :
    Real.log x/2≤Real.log (x/2) := by
  rw [Real.log_div hx.ne' (by norm_num : (2:ℝ)≠0)]
  linarith

/-- Uniform comparability across a dyadic interval for the actual
triple-logarithmic scale. -/
theorem slowScale_half_lower :
    ∀ᶠ t in atTop,slowScale t/2≤slowScale (t/2) := by
  have hlog := Real.tendsto_log_atTop
  have hloglog := hlog.comp hlog
  filter_upwards [eventually_gt_atTop (0:ℝ),hlog.eventually (eventually_gt_atTop (0:ℝ)),
    hlog.eventually (eventually_ge_atTop (2*Real.log 2)),
    hloglog.eventually (eventually_gt_atTop (0:ℝ)),
    hloglog.eventually (eventually_ge_atTop (2*Real.log 2)),
    slowScale_tendsto.eventually (eventually_ge_atTop (2*Real.log 2))]
    with t ht hl1 hl1b hl2 hl2b hl3b
  have h₁ := log_half_lower ht hl1b
  have h₂ := (log_half_lower hl1 hl2b).trans
    (Real.log_le_log (by positivity : 0<Real.log t/2) h₁)
  have h₃ := (log_half_lower hl2 hl3b).trans
    (Real.log_le_log (by positivity : 0<Real.log (Real.log t)/2) h₂)
  exact h₃

theorem fourthRootScale_half_lower :
    ∀ᶠ t in atTop,fourthRootScale t/2≤fourthRootScale (t/2) := by
  filter_upwards [slowScale_half_lower,
    slowScale_tendsto.eventually (eventually_ge_atTop (0:ℝ))] with t hh ht
  have hhalf : 0≤slowScale (t/2) := (by positivity : 0≤slowScale t/2).trans hh
  apply (pow_le_pow_iff_left₀
    (show 0≤fourthRootScale t/2 by unfold fourthRootScale; positivity)
    (show 0≤fourthRootScale (t/2) by unfold fourthRootScale; positivity)
    (by norm_num : (4:ℕ)≠0)).mp
  rw [div_pow,fourthRootScale_pow_four ht,fourthRootScale_pow_four hhalf]
  norm_num
  linarith

theorem fourthRootScale_mono {s t : ℝ} (hs : 0<s) (hs1 : 0<Real.log s)
    (hs2 : 0<Real.log (Real.log s)) (hst : s≤t) :
    fourthRootScale s≤fourthRootScale t := by
  apply Real.sqrt_le_sqrt
  apply Real.sqrt_le_sqrt
  exact Real.log_le_log hs2 (Real.log_le_log hs1 (Real.log_le_log hs hst))

/-- Every centre in the dyadic interval has at least half the central
fourth-root scale, with one threshold valid for all such centres. -/
theorem fourthRootScale_uniform_centres :
    ∀ᶠ t in atTop,∀ s : ℝ,t/2≤s → fourthRootScale t/2≤fourthRootScale s := by
  have hh : Tendsto (fun t : ℝ => t/2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num : (0:ℝ)<2) tendsto_id
  filter_upwards [fourthRootScale_half_lower,
    hh.eventually (eventually_gt_atTop (0:ℝ)),
    (Real.tendsto_log_atTop.comp hh).eventually (eventually_gt_atTop (0:ℝ)),
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hh)).eventually
      (eventually_gt_atTop (0:ℝ))] with t ht h0 h1 h2
  intro s hs
  exact ht.trans (fourthRootScale_mono h0 h1 h2 hs)

#print axioms log_half_lower
#print axioms slowScale_half_lower
#print axioms fourthRootScale_half_lower
#print axioms fourthRootScale_mono
#print axioms fourthRootScale_uniform_centres

end QuantitativeMaass
