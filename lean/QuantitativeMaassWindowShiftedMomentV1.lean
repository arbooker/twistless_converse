module

public import QuantitativeMaassPositiveWindowKernelV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace QuantitativeMaass

/-- The shifted fifth moment is dominated by the zeroth and fifth
moments of the actual positive smoothing kernel. -/
theorem scaledWindowKernel_fifth_shifted_pointwise (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x, 0 ≤ K x) (R : ℝ) (hR : 0 < R) (x : ℝ) :
    (1+|x|)^5 * scaledWindowKernel K R x ≤
      16 * (scaledWindowKernel K R x + |x|^5 * scaledWindowKernel K R x) := by
  have h := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg x) 5
  norm_num at h
  have hκ : 0 ≤ scaledWindowKernel K R x := mul_nonneg hR.le (hK _)
  apply (mul_le_mul_of_nonneg_right h hκ).trans_eq
  ring

theorem scaledWindowKernel_fifth_shifted_integrable (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x, 0 ≤ K x) (R : ℝ) (hR : 0 < R) :
    Integrable (fun x => (1+|x|)^5 * scaledWindowKernel K R x) := by
  have hi := ((scaledWindowKernel_integrable K R hR).add
    (scaledWindowKernel_moment_integrable K hK R hR 5)).const_mul 16
  apply hi.mono' (by unfold scaledWindowKernel; fun_prop)
  filter_upwards with x
  rw [Real.norm_of_nonneg (by
    exact mul_nonneg (by positivity) (mul_nonneg hR.le (hK _)))]
  exact scaledWindowKernel_fifth_shifted_pointwise K hK R hR x

/-- A constant chosen before the smoothing scale controls the fifth
moment for every R at least one. -/
theorem scaledWindowKernel_fifth_shifted_uniform (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1) (R : ℝ) (hR : 1 ≤ R) :
    (∫ x, (1+|x|)^5 * scaledWindowKernel K R x) ≤
      16 * (1 + ∫ x, |x|^5 * K x) := by
  have hR0 : 0 < R := by linarith
  have hi0 := scaledWindowKernel_integrable K R hR0
  have hi5 := scaledWindowKernel_moment_integrable K hK R hR0 5
  have hM : 0 ≤ ∫ x, |x|^5 * K x :=
    integral_nonneg (fun x => mul_nonneg (by positivity) (hK x))
  calc
    _ ≤ ∫ x, 16 * (scaledWindowKernel K R x + |x|^5 * scaledWindowKernel K R x) :=
      integral_mono (scaledWindowKernel_fifth_shifted_integrable K hK R hR0)
        ((hi0.add hi5).const_mul 16) (scaledWindowKernel_fifth_shifted_pointwise K hK R hR0)
    _ = 16 * (1 + (∫ x, |x|^5 * K x)/R^5) := by
      rw [integral_const_mul, integral_add hi0 hi5,
        scaledWindowKernel_mass_one K hm R hR0, scaledWindowKernel_moment K R hR0 5]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl (div_le_self hM (one_le_pow₀ hR))) (by norm_num)

#print axioms scaledWindowKernel_fifth_shifted_integrable
#print axioms scaledWindowKernel_fifth_shifted_uniform

end QuantitativeMaass
