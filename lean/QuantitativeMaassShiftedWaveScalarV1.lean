module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace QuantitativeMaass.Wave

/-- The real shifted wave multiplier, including the exceptional spectrum. -/
def signedCosine (t x : ℝ) : ℝ :=
  Real.cos (t * Real.sqrt x) + Real.cosh (t * Real.sqrt (-x)) - 1

theorem signedCosine_nonneg_energy (t x : ℝ) (hx : 0 ≤ x) :
    signedCosine t x = Real.cos (t * Real.sqrt x) := by
  simp [signedCosine, Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr hx)]

theorem signedCosine_nonpos_energy (t x : ℝ) (hx : x ≤ 0) :
    signedCosine t x = Real.cosh (t * Real.sqrt (-x)) := by
  simp [signedCosine, Real.sqrt_eq_zero_of_nonpos hx]

theorem signedCosine_continuous (t : ℝ) : Continuous (signedCosine t) := by
  unfold signedCosine
  fun_prop

theorem signedCosine_bound (t x : ℝ) (hx : -(1/4 : ℝ) ≤ x) :
    ‖signedCosine t x‖ ≤ Real.cosh (|t| / 2) := by
  by_cases h : 0 ≤ x
  · rw [signedCosine_nonneg_energy t x h, Real.norm_eq_abs]
    exact (Real.abs_cos_le_one _).trans (Real.one_le_cosh _)
  · rw [signedCosine_nonpos_energy t x (le_of_not_ge h), Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos _)]
    apply Real.cosh_le_cosh.mpr
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (div_nonneg (abs_nonneg t) (show (0 : ℝ) ≤ 2 by norm_num))]
    have hs : Real.sqrt (-x) ≤ 1/2 := by
      apply (Real.sqrt_le_iff).mpr
      constructor <;> nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg t)]

/-- A continuous extension off the inverse spectrum. The maximum ensures the
exceptional energy is bounded below by -1/4 even on the negative half-line. -/
def shiftedDampedCosine (t s : ℝ) : ℝ :=
  s * signedCosine t (max (s⁻¹ - 1) 0 - 1/4)

theorem shiftedDampedCosine_norm_le (t s : ℝ) :
    ‖shiftedDampedCosine t s‖ ≤ Real.cosh (|t|/2) * ‖s‖ := by
  rw [shiftedDampedCosine, norm_mul, mul_comm (Real.cosh _) ‖s‖]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
  apply signedCosine_bound
  linarith [le_max_right (s⁻¹-1) (0 : ℝ)]

theorem shiftedDampedCosine_continuous (t : ℝ) : Continuous (shiftedDampedCosine t) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : s = 0
  · subst s
    change Tendsto (shiftedDampedCosine t) (𝓝 0) (𝓝 (shiftedDampedCosine t 0))
    have hz : shiftedDampedCosine t 0 = 0 := by simp [shiftedDampedCosine]
    rw [hz]
    apply squeeze_zero_norm (shiftedDampedCosine_norm_le t)
    have hc : Continuous (fun s : ℝ => Real.cosh (|t|/2) * ‖s‖) :=
      continuous_const.mul continuous_norm
    simpa using hc.continuousAt (x := 0) |>.tendsto
  · exact continuousAt_id.mul ((signedCosine_continuous t).continuousAt.comp
      (((continuousAt_id.inv₀ hs).sub continuousAt_const).max
        continuousAt_const |>.sub continuousAt_const))

theorem shiftedDampedCosine_zero : shiftedDampedCosine 0 = id := by
  ext s
  simp [shiftedDampedCosine, signedCosine]

theorem shiftedDampedCosine_neg (t : ℝ) :
    shiftedDampedCosine (-t) = shiftedDampedCosine t := by
  ext s
  simp [shiftedDampedCosine, signedCosine]

theorem shiftedDampedCosine_on_spectrum (t s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    shiftedDampedCosine t s = s * signedCosine t (s⁻¹ - 1 - 1/4) := by
  have hi : 1 ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  simp [shiftedDampedCosine, max_eq_left (sub_nonneg.mpr hi)]

#print axioms signedCosine_bound
#print axioms shiftedDampedCosine_continuous
#print axioms shiftedDampedCosine_on_spectrum

end QuantitativeMaass.Wave
