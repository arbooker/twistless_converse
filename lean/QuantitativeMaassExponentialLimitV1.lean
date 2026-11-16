module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass.Weighted

/-- A nonnegative quantity dominated by every exponentially decaying bound
vanishes. This is the scalar limiting step in weighted-energy propagation. -/
theorem eq_zero_of_exponential_bounds {r C δ : ℝ} (hr : 0≤r) (hδ : 0<δ)
    (h : ∀ a : ℝ, 0≤a → r≤C*Real.exp (-δ*a)) : r=0 := by
  have ht : Tendsto (fun a : ℝ => C*Real.exp (-δ*a)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hδ))
    simpa using he.const_mul C
  exact le_antisymm (ge_of_tendsto ht (eventually_atTop.2 ⟨0,h⟩)) hr

#print axioms eq_zero_of_exponential_bounds

end QuantitativeMaass.Weighted
