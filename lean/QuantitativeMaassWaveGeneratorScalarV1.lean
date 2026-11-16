module

public import QuantitativeMaassWaveMultiplierV1
public import QuantitativeMaassWaveTaylorV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeMaass.Wave

/-- Twice the cosine difference quotient, damped by two resolvent factors,
with the Laplacian term added back. -/
def weightedCosineRemainder (t s : ℝ) : ℝ :=
  (2/t^2)*(dampedCosine t s*s-s^2)+(s-s^2)

theorem weightedCosineRemainder_continuous (t : ℝ) :
    Continuous (weightedCosineRemainder t) := by
  exact (continuous_const.mul (((dampedCosine_continuous t).mul continuous_id).sub
    (continuous_id.pow 2))).add (continuous_id.sub (continuous_id.pow 2))

/-- A uniform second-difference error on the whole inverse spectral
interval, including its singular endpoint. -/
theorem weightedCosineRemainder_bound {t s : ℝ} (ht : t≠0) (hs : 0≤s) (hs1 : s≤1) :
    ‖weightedCosineRemainder t s‖≤6*t^2 := by
  by_cases hs0 : s=0
  · subst s
    simp only [weightedCosineRemainder,dampedCosine,zero_mul,mul_zero,zero_pow (by norm_num : 2≠0),
      sub_self,add_zero,norm_zero]
    positivity
  have hspos : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hfreq : s*(Real.sqrt (s⁻¹-1))^2=1-s := by
    rw [Real.sq_sqrt (by have := (one_le_inv₀ hspos).mpr hs1; linarith),mul_sub,mul_inv_cancel₀ hs0,mul_one]
  have he : weightedCosineRemainder t s=(2*s^2/t^2)*
      (Real.cos (t*Real.sqrt (s⁻¹-1))-(1-(t*Real.sqrt (s⁻¹-1))^2/2)) := by
    unfold weightedCosineRemainder dampedCosine
    have hh : s⁻¹-1=(1-s)/s := by field_simp
    have hfreq' := hfreq
    rw [hh] at hfreq'
    field_simp [ht]
    nlinarith [congrArg (fun z : ℝ => t^2*z) hfreq']
  rw [he,norm_mul,Real.norm_eq_abs (2*s^2/t^2),abs_of_nonneg (by positivity),Real.norm_eq_abs]
  calc
    (2*s^2/t^2)*|Real.cos (t*Real.sqrt (s⁻¹-1))-(1-(t*Real.sqrt (s⁻¹-1))^2/2)|
        ≤ (2*s^2/t^2)*(3*(t*Real.sqrt (s⁻¹-1))^4) :=
      mul_le_mul_of_nonneg_left (cosine_fourth_remainder _) (by positivity)
    _ = 6*t^2*(1-s)^2 := by
      rw [← hfreq]
      field_simp [ht]
      ring
    _ ≤ 6*t^2 := by
      have h : (1-s)^2≤1 := by nlinarith
      nlinarith [sq_nonneg t]

#print axioms weightedCosineRemainder_bound

end QuantitativeMaass.Wave
