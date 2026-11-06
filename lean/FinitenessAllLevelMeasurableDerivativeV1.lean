module

public import FinitenessAllLevelFormalMeasurableV1
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelMeasurableDerivative

open Complex Set Filter MeasureTheory
open scoped Topology

/-- Differentiating a measurable family in its complex parameter preserves
measurability in the integration variable. Spatial continuity is unnecessary. -/
theorem measurable_derivative {α : Type*} [MeasurableSpace α]
    (H : ℂ → α → ℂ) (hH : ∀ w, Measurable (H w)) (w : ℂ)
    (hd : ∀ z, DifferentiableAt ℂ (fun v => H v z) w) :
    Measurable (fun z => deriv (fun v => H v z) w) := by
  let t : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1)
  have ht0 : Tendsto t atTop (𝓝 (0 : ℂ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto t atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht0, Filter.Eventually.of_forall (fun n => ?_)⟩
    change 1 / ((n : ℂ) + 1) ≠ 0
    apply one_div_ne_zero
    exact_mod_cast (Nat.succ_ne_zero n)
  apply measurable_of_tendsto_metrizable
    (f := fun n z => (t n)⁻¹ • (H (w + t n) z - H w z))
    (fun n => ((hH (w + t n)).sub (hH w)).const_smul ((t n)⁻¹))
  apply tendsto_pi_nhds.mpr
  intro z
  exact (hd z).hasDerivAt.tendsto_slope_zero.comp ht

#print axioms measurable_derivative

end FinitenessAllLevelMeasurableDerivative
