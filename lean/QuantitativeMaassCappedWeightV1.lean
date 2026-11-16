module

public import AsymptoticWeightedBranchesV1
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

set_option autoImplicit false
@[expose] public noncomputable section

open UpperHalfPlane

namespace QuantitativeMaass

/-- The actual capped height weight used in the original reconstruction. -/
def cappedHeightWeight (ε : ℝ) (t : ℕ) (z : ℍ) : ℝ := (min (z.im/ε) 1)^t

theorem cappedHeightWeight_pos {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) :
    0<cappedHeightWeight ε t z := pow_pos (lt_min (div_pos z.im_pos hε) zero_lt_one) t

theorem cappedHeightWeight_log {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) :
    Real.log (cappedHeightWeight ε t z)=
      (t:ℝ)*min (Real.log z.im-Real.log ε) 0 := by
  rw [cappedHeightWeight,Real.log_pow]
  congr 1
  rw [←Real.log_div z.im_ne_zero hε.ne']
  by_cases h : z.im/ε≤1
  · rw [min_eq_left h,min_eq_left]
    exact (Real.log_le_log_iff (div_pos z.im_pos hε) zero_lt_one).mpr h |>.trans_eq Real.log_one
  · rw [min_eq_right (le_of_not_ge h),Real.log_one,min_eq_right (Real.log_nonneg (le_of_not_ge h))]

/-- The logarithm of the concrete capped weight is globally Lipschitz for
hyperbolic distance, including across the cap. The bound is uniform in ε. -/
theorem cappedHeightWeight_log_dist {ε : ℝ} (hε : 0<ε) (t : ℕ) (z w : ℍ) :
    |Real.log (cappedHeightWeight ε t z)-Real.log (cappedHeightWeight ε t w)|≤
      (t:ℝ)*dist z w := by
  rw [cappedHeightWeight_log hε,cappedHeightWeight_log hε,←mul_sub,abs_mul,
    abs_of_nonneg (Nat.cast_nonneg t)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg t)
  have hm := abs_min_sub_min_le_max (Real.log z.im-Real.log ε) 0
    (Real.log w.im-Real.log ε) 0
  simp only [sub_self,abs_zero,sub_sub_sub_cancel_right,
    max_eq_left (abs_nonneg (Real.log z.im-Real.log w.im))] at hm
  exact hm.trans (by simpa only [Real.dist_eq] using UpperHalfPlane.dist_log_im_le z w)

/-- Concrete exponential distortion on every propagation ball. -/
theorem cappedHeightWeight_ratio_bound {ε : ℝ} (hε : 0<ε) (t : ℕ) (z w : ℍ) :
    cappedHeightWeight ε t z/cappedHeightWeight ε t w≤Real.exp ((t:ℝ)*dist z w) := by
  rw [←Real.exp_log (div_pos (cappedHeightWeight_pos hε t z) (cappedHeightWeight_pos hε t w)),
    Real.exp_le_exp,Real.log_div (cappedHeightWeight_pos hε t z).ne' (cappedHeightWeight_pos hε t w).ne']
  exact (le_abs_self _).trans (cappedHeightWeight_log_dist hε t z w)

/-- This weight is exactly the scalar multiplying the physical Maass wave. -/
theorem weighted_zero_eq_capped (ε : ℝ) (t : ℕ) (F : ℂ → ℂ) (z : ℍ) :
    AsymptoticWeightedBranches.weighted ε t 0 F z=(cappedHeightWeight ε t z:ℂ)*F z := by
  simp only [AsymptoticWeightedBranches.weighted,cappedHeightWeight,pow_zero,mul_one]

#print axioms cappedHeightWeight_log
#print axioms cappedHeightWeight_log_dist
#print axioms cappedHeightWeight_ratio_bound
#print axioms weighted_zero_eq_capped

end QuantitativeMaass
