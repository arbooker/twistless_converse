module

public import QuantitativeMaassBroadMultiplierV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology SchwartzMap

namespace QuantitativeMaass

/-- The first absolute moment of a translated and dilated Schwartz profile.
The bound retains one power of the central frequency and two of the width. -/
theorem translatedSchwartz_first_moment (F : SchwartzMap ℝ ℂ)
    (L : ℝ) (hL : 0 < L) (t : ℝ) :
    Integrable (fun r : ℝ => |r| * ‖F ((r-t)/L)‖) ∧
    (∫ r : ℝ, |r| * ‖F ((r-t)/L)‖) ≤
      L * (|t| * (∫ u : ℝ, ‖F u‖) + L * (∫ u : ℝ, |u| * ‖F u‖)) := by
  have hzero : Integrable (fun u : ℝ => ‖F u‖) := F.integrable.norm
  have hone : Integrable (fun u : ℝ => |u| * ‖F u‖) := by
    simpa only [pow_one, Real.norm_eq_abs] using F.integrable_pow_mul volume 1
  let g : ℝ → ℝ := fun u => |t| * ‖F u‖ + L * (|u| * ‖F u‖)
  have hg : Integrable g := (hzero.const_mul _).add (hone.const_mul _)
  have hshift : Integrable (fun r : ℝ => g ((r-t)/L)) :=
    (hg.comp_div hL.ne').comp_sub_right t
  have hbound (r : ℝ) : |r| * ‖F ((r-t)/L)‖ ≤ g ((r-t)/L) := by
    have ha : |r| ≤ |t| + L * |(r-t)/L| := by
      rw [abs_div, abs_of_pos hL, mul_div_cancel₀ _ hL.ne']
      have hh := abs_add_le (r-t) t
      rw [sub_add_cancel] at hh
      linarith
    have hb := mul_le_mul_of_nonneg_right ha (norm_nonneg (F ((r-t)/L)))
    dsimp [g]
    nlinarith
  have hi : Integrable (fun r : ℝ => |r| * ‖F ((r-t)/L)‖) :=
    hshift.mono' (by fun_prop) (Filter.Eventually.of_forall (fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbound r))
  refine ⟨hi, (integral_mono hi hshift hbound).trans_eq ?_⟩
  rw [integral_sub_right_eq_self (fun u : ℝ => g (u/L)) t,
    Measure.integral_comp_div g L, abs_of_pos hL]
  simp only [g, smul_eq_mul, integral_add (hzero.const_mul _) (hone.const_mul _),
    integral_const_mul]

#print axioms translatedSchwartz_first_moment

end QuantitativeMaass
