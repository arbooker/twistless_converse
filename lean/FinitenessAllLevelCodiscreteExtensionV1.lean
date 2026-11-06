module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Topology.DiscreteSubset

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter
open scoped Topology

/-- Holomorphic functions on a codiscrete planar domain with a global
polynomial bound extend to entire functions with the SAME bound. -/
theorem codiscrete_entire_extension {G : Set ℂ} (hG : G ∈ codiscrete ℂ)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f G) {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (hb : ∀ z ∈ G, ‖f z‖ ≤ C * (1 + ‖z‖) ^ k) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ EqOn g f G ∧
      ∀ z, ‖g z‖ ≤ C * (1 + ‖z‖) ^ k := by
  classical
  let g : ℂ → ℂ := fun z => limUnder (𝓝[≠] z) f
  have heq : EqOn g f G := by
    intro z hz
    exact ((hf z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  have hp (w : ℂ) : ∀ᶠ z in 𝓝[≠] w, z ∈ G :=
    mem_codiscrete_iff_forall_mem_nhdsNE.mp hG w
  have hd : Differentiable ℂ g := by
    intro w
    have hne : ∀ᶠ z in 𝓝 w, z ≠ w → z ∈ G := by
      simpa only [mem_compl_iff, mem_singleton_iff] using eventually_nhdsWithin_iff.mp (hp w)
    have hnorm : ∀ᶠ z in 𝓝 w, ‖z‖ < ‖w‖ + 1 :=
      (continuous_norm.continuousAt).eventually_lt_const (by linarith)
    let S := {z : ℂ | (z ≠ w → z ∈ G) ∧ ‖z‖ < ‖w‖ + 1}
    have hS : S ∈ 𝓝 w := hne.and hnorm
    have hdiff : DifferentiableOn ℂ f (S \ {w}) := by
      intro z hz
      exact (hf z (hz.1.1 hz.2)).differentiableAt.differentiableWithinAt
    have hbounded : BddAbove ((norm ∘ f) '' (S \ {w})) := by
      refine ⟨C * (1 + (‖w‖ + 1)) ^ k, ?_⟩
      rintro y ⟨z, hz, rfl⟩
      apply (hb z (hz.1.1 hz.2)).trans
      apply mul_le_mul_of_nonneg_left _ hC
      exact pow_le_pow_left₀ (by positivity) (by linarith [hz.1.2]) k
    have hu := (Complex.differentiableOn_update_limUnder_of_bddAbove hS hdiff hbounded).differentiableAt hS
    apply hu.congr_of_eventuallyEq
    filter_upwards [hne] with z hz
    by_cases hzw : z = w
    · subst z
      simp only [Function.update_self, g]
    · rw [Function.update_of_ne hzw]
      exact heq (hz hzw)
  refine ⟨g, hd, heq, fun w => ?_⟩
  have hg : Tendsto (fun z => ‖g z‖) (𝓝[≠] w) (𝓝 ‖g w‖) :=
    (hd w).continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds
  have hbound : Tendsto (fun z : ℂ => C * (1 + ‖z‖) ^ k) (𝓝[≠] w)
      (𝓝 (C * (1 + ‖w‖) ^ k)) := by
    apply ContinuousAt.tendsto (by fun_prop) |>.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hg hbound
  filter_upwards [hp w] with z hz
  rw [heq hz]
  exact hb z hz

#print axioms codiscrete_entire_extension

end FinitenessAllLevelPolynomialPresentation
