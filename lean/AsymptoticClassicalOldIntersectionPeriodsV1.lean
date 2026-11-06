module

public import AsymptoticClassicalOldIntersectionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Filter Topology
open scoped ModularForm Manifold

/-- A holomorphic function with nonzero real periods accumulating at zero
 is constant, by the identity theorem on the upper half-plane. -/
theorem constant_of_small_periods {f : ℍ → ℂ} (hf : MDiff f)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) (hne : ∀ n, r n ≠ 0)
    (hperiod : ∀ n z, f (r n +ᵥ z) = f z) (z₀ : ℍ) :
    f = fun _ => f z₀ := by
  have ht : Tendsto (fun n => r n +ᵥ z₀) atTop (𝓝 z₀) := by
    apply UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff.mpr
    simpa only [Function.comp_def, UpperHalfPlane.coe_vadd, Complex.ofReal_zero, zero_add]
      using ((Complex.continuous_ofReal.tendsto 0).comp hr).add_const (z₀ : ℂ)
  have ht' : Tendsto (fun n => r n +ᵥ z₀) atTop (𝓝[≠] z₀) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht, Filter.Eventually.of_forall fun n => ?_⟩
    change r n +ᵥ z₀ ≠ z₀
    intro he
    apply hne n
    exact (UpperHalfPlane.vadd_right_cancel_iff z₀).mp (he.trans (zero_vadd ℝ z₀).symm)
  have he : (fun z => f z - f z₀) = 0 := by
    apply UpperHalfPlane.eq_zero_of_frequently (hf.sub mdifferentiable_const) (τ := z₀)
    refine Filter.Frequently.filter_mono ?_ ht'
    rw [Filter.frequently_map]
    exact (Filter.Eventually.of_forall fun n => sub_eq_zero.mpr (hperiod n z₀)).frequently
  funext z
  exact sub_eq_zero.mp (congrFun he z)

/-- Cusp decay eliminates the constant produced by accumulating periods. -/
theorem zero_of_small_periods {f : ℍ → ℂ} (hf : MDiff f)
    (hzero : IsZeroAtImInfty f)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) (hne : ∀ n, r n ≠ 0)
    (hperiod : ∀ n z, f (r n +ᵥ z) = f z) : f = 0 := by
  have he := constant_of_small_periods hf r hr hne hperiod UpperHalfPlane.I
  rw [he] at hzero
  have hc : f UpperHalfPlane.I = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
  rw [he, hc]
  rfl

#print axioms constant_of_small_periods
#print axioms zero_of_small_periods

end AsymptoticClassicalCusp
