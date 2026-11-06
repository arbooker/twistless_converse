module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars

private theorem normalized_power_bound (b α : ℝ) (hb : 0<b) (hb16 : b≤16)
    (hα : 2≤α) : b^α≤(b/16)^2*(16:ℝ)^α := by
  have h := Real.rpow_le_rpow_of_exponent_ge
    (show 0<b/16 by positivity) ((div_le_one (by norm_num)).2 hb16) hα
  rw [Real.rpow_two, Real.div_rpow hb.le (by norm_num)] at h
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num) α)).mp h

/-- The shifted first scalar row cannot vanish two or more steps to the
right: its leading exponential dominates all three remaining terms. -/
theorem shifted_exponential_dominance (α : ℝ) (hα : 2≤α) :
    (9/4:ℝ)*(4:ℝ)^α+(2:ℝ)^α+(9:ℝ)^α < (16:ℝ)^α := by
  have h4 := normalized_power_bound 4 α (by norm_num) (by norm_num) hα
  have h2 := normalized_power_bound 2 α (by norm_num) (by norm_num) hα
  have h9 := normalized_power_bound 9 α (by norm_num) (by norm_num) hα
  have hp := Real.rpow_pos_of_pos (show (0:ℝ)<16 by norm_num) α
  norm_num at h4 h2 h9
  linarith

#print axioms shifted_exponential_dominance
end QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars
