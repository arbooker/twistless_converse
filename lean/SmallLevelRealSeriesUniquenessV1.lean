module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Analytic.IsolatedZeros

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Filter Set Metric FormalMultilinearSeries
open scoped Topology

theorem analytic_real_interval_unique {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    {δ : ℝ} (hδ : 0<δ) (he : ∀ t : ℝ, 0<t → t<δ → f (t:ℂ)=g (t:ℂ)) :
    f=ᶠ[𝓝 0] g := by
  apply (hf.frequently_eq_iff_eventually_eq hg).mp
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨V,hV,hVU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hU
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hV
  let t : ℝ := min δ ε/2
  have ht : 0<t := by dsimp [t]; positivity
  have htδ : t<δ := by dsimp [t]; linarith [min_le_left δ ε]
  have htε : t<ε := by dsimp [t]; linarith [min_le_right δ ε]
  refine ⟨(t:ℂ),hVU ⟨hball ?_,?_⟩,he t ht htδ⟩
  · simpa only [Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht] using htε
  · simpa only [Set.mem_compl_iff,Set.mem_singleton_iff,Complex.ofReal_eq_zero] using ne_of_gt ht

/-- Equality on a real interval suffices to identify every complex Taylor
coefficient with the coefficient of the binomial series. -/
theorem coefficients_of_real_binomial {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt f p 0) (A w : ℂ) {δ : ℝ} (hδ : 0<δ)
    (he : ∀ t : ℝ, 0<t → t<δ → f (t:ℂ)=A*(1+(t:ℂ))^w) (n : ℕ) :
    p.coeff n=A*Ring.choose w n := by
  have hq : HasFPowerSeriesAt (fun z : ℂ => A*(1+z)^w) (A • binomialSeries ℂ w) 0 := by
    simpa only [Pi.smul_def,smul_eq_mul] using
      (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := w)).const_smul (c := A)
  have h := hp.eq_formalMultilinearSeries_of_eventually hq
    (analytic_real_interval_unique hp.analyticAt hq.analyticAt hδ he)
  rw [h]
  simp [FormalMultilinearSeries.coeff,Pi.one_def,binomialSeries,
    FormalMultilinearSeries.ofScalars]


#print axioms analytic_real_interval_unique
#print axioms coefficients_of_real_binomial
end SmallLevelTaylor
