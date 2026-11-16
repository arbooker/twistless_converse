module

public import QuantitativeMaassWaveGeneratorScalarV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeMaass.Wave

/-- The second time difference with one resolvent factor. -/
def dampedSecondDifference (t s : ℝ) : ℝ := (2/t^2)*(dampedCosine t s-s)

theorem dampedSecondDifference_continuous (t : ℝ) : Continuous (dampedSecondDifference t) :=
  continuous_const.mul ((dampedCosine_continuous t).sub continuous_id)

/-- Uniform bound including totalized time zero; it is this one-resolvent
estimate that extends the generator limit to the entire operator domain. -/
theorem dampedSecondDifference_bound (t : ℝ) {s : ℝ} (hs : 0≤s) (hs1 : s≤1) :
    ‖dampedSecondDifference t s‖≤1-s := by
  by_cases ht : t=0
  · subst t
    simp only [dampedSecondDifference,zero_pow (by norm_num : 2≠0),div_zero,zero_mul,norm_zero]
    exact sub_nonneg.mpr hs1
  by_cases hs0 : s=0
  · subst s
    simp [dampedSecondDifference,dampedCosine]
  have hspos : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hfreq : s*(Real.sqrt (s⁻¹-1))^2=1-s := by
    rw [Real.sq_sqrt (by have := (one_le_inv₀ hspos).mpr hs1; linarith),mul_sub,mul_inv_cancel₀ hs0,mul_one]
  have he : dampedSecondDifference t s=(2/t^2)*s*
      (Real.cos (t*Real.sqrt (s⁻¹-1))-1) := by unfold dampedSecondDifference dampedCosine; ring
  rw [he,norm_mul,Real.norm_eq_abs (2/t^2*s),abs_of_nonneg (by positivity),Real.norm_eq_abs]
  calc
    (2/t^2*s)*|Real.cos (t*Real.sqrt (s⁻¹-1))-1|
        ≤ (2/t^2*s)*((t*Real.sqrt (s⁻¹-1))^2/2) :=
      mul_le_mul_of_nonneg_left (cosine_second_bound _) (by positivity)
    _ = s*(Real.sqrt (s⁻¹-1))^2 := by field_simp [ht]
    _ = 1-s := hfreq

#print axioms dampedSecondDifference_bound

end QuantitativeMaass.Wave
