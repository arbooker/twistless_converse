module

public import QuantitativeMaassWeightedWidthDecayV1
public import QuantitativeMaassFiniteEnergyTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass

/-- The extra exponential weight absorbs the inverse width lost when
turning a squared Hilbert--Schmidt estimate into a linear trace estimate. -/
theorem weighted_energy_trace_limit (ε E F : ℝ → ℝ) (C : ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hE : Tendsto (fun t => Real.exp (fourthRootScale t)*E t/(t*ε t)) atTop (𝓝 0))
    (hF : ∀ᶠ t in atTop,(F t)^2≤C*t*E t) :
    Tendsto (fun t => F t/(t*ε t)) atTop (𝓝 0) := by
  have hh := (weighted_energy_two_widths ε E hε hproduct hE).const_mul C
  simp only [mul_zero] at hh
  have hs : Tendsto (fun t => (F t/(t*ε t))^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun t => sq_nonneg _)) _ hh
    filter_upwards [hε,hF,eventually_gt_atTop (0:ℝ)] with t he hf ht
    rw [div_pow]
    calc
      _ ≤ C*t*E t/(t*ε t)^2 := div_le_div_of_nonneg_right hf (sq_nonneg _)
      _ = C*(E t/(t*(ε t)^2)) := by
        field_simp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hz := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,Real.sqrt_zero,Real.norm_eq_abs] using hz

#print axioms weighted_energy_trace_limit

end QuantitativeMaass
