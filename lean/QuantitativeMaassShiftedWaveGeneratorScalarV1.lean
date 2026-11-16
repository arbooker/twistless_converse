module

public import QuantitativeMaassShiftedWaveTaylorV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace QuantitativeMaass.Wave

def shiftedWeightedRemainder (t s : ℝ) : ℝ :=
  (2/t^2)*(shiftedDampedCosine t s*s-s^2)+(s-(5/4)*s^2)

theorem shiftedWeightedRemainder_continuous (t : ℝ) :
    Continuous (shiftedWeightedRemainder t) := by
  exact (continuous_const.mul (((shiftedDampedCosine_continuous t).mul continuous_id).sub
    (continuous_id.pow 2))).add (continuous_id.sub (continuous_const.mul (continuous_id.pow 2)))

/-- Uniform error on the full inverse spectrum, including the zero endpoint. -/
theorem shiftedWeightedRemainder_bound {t s : ℝ} (ht : t≠0) (ht1 : |t|≤1)
    (hs : 0≤s) (hs1 : s≤1) : ‖shiftedWeightedRemainder t s‖≤6*t^2 := by
  by_cases hs0 : s=0
  · subst s
    simp [shiftedWeightedRemainder,shiftedDampedCosine]
    positivity
  have hspos : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hx : -(1/4 : ℝ) ≤ s⁻¹-1-1/4 := by
    have := (one_le_inv₀ hspos).mpr hs1
    linarith
  have hf : s*(s⁻¹-1-1/4)=1-(5/4)*s := by field_simp; ring
  have he : shiftedWeightedRemainder t s=(2*s^2/t^2)*
      (signedCosine t (s⁻¹-1-1/4)-(1-t^2*(s⁻¹-1-1/4)/2)) := by
    unfold shiftedWeightedRemainder
    rw [shiftedDampedCosine_on_spectrum t s hspos hs1]
    field_simp [ht,hs0]
    ring
  rw [he,norm_mul,Real.norm_eq_abs (2*s^2/t^2),abs_of_nonneg (by positivity),Real.norm_eq_abs]
  calc
    _ ≤ (2*s^2/t^2)*(3*t^4*(s⁻¹-1-1/4)^2) :=
      mul_le_mul_of_nonneg_left (signedCosine_fourth_remainder ht1 hx) (by positivity)
    _ = 6*t^2*(1-(5/4)*s)^2 := by rw [← hf]; field_simp [ht]; ring
    _ ≤ 6*t^2 := by
      have h : (1-(5/4)*s)^2≤1 := by nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1)]
      nlinarith [sq_nonneg t]

def shiftedDampedSecondDifference (t s : ℝ) : ℝ :=
  (2/t^2)*(shiftedDampedCosine t s-s)

theorem shiftedDampedSecondDifference_continuous (t : ℝ) :
    Continuous (shiftedDampedSecondDifference t) :=
  continuous_const.mul ((shiftedDampedCosine_continuous t).sub continuous_id)

/-- One resolvent factor suffices for a uniform local bound. -/
theorem shiftedDampedSecondDifference_bound {t s : ℝ} (ht1 : |t|≤1)
    (hs : 0≤s) (hs1 : s≤1) : ‖shiftedDampedSecondDifference t s‖≤4 := by
  by_cases ht : t=0
  · subst t
    norm_num [shiftedDampedSecondDifference]
  by_cases hs0 : s=0
  · subst s
    norm_num [shiftedDampedSecondDifference,shiftedDampedCosine]
  have hspos : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hx : -(1/4 : ℝ) ≤ s⁻¹-1-1/4 := by
    have := (one_le_inv₀ hspos).mpr hs1
    linarith
  have hf : s*(s⁻¹-1-1/4)=1-(5/4)*s := by field_simp; ring
  have he : shiftedDampedSecondDifference t s=(2/t^2*s)*
      (signedCosine t (s⁻¹-1-1/4)-1) := by
    unfold shiftedDampedSecondDifference
    rw [shiftedDampedCosine_on_spectrum t s hspos hs1]
    ring
  rw [he,norm_mul,Real.norm_eq_abs (2/t^2*s),abs_of_nonneg (by positivity),Real.norm_eq_abs]
  calc
    _ ≤ (2/t^2*s)*(2*t^2*|s⁻¹-1-1/4|) :=
      mul_le_mul_of_nonneg_left (signedCosine_second_bound ht1 hx) (by positivity)
    _ = 4*|1-(5/4)*s| := by
      rw [← hf,abs_mul,abs_of_nonneg hs]
      field_simp [ht]
      ring
    _ ≤ 4 := by
      have h : |1-(5/4)*s|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
      linarith

#print axioms shiftedWeightedRemainder_bound
#print axioms shiftedDampedSecondDifference_bound

end QuantitativeMaass.Wave
