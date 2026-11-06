module

public import QuantitativeHolomorphicCompactBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane

/-- Uniform positive denominator bound on a horizontal half-plane, with
the upper-triangular case treated separately. -/
def compactDenominatorLower (g : GL (Fin 2) ℝ) (η : ℝ) : ℝ :=
  if g 1 0 = 0 then |g 1 1| else |g 1 0| * η

theorem compactDenominatorLower_pos (g : GL (Fin 2) ℝ) {η : ℝ} (hη : 0<η) :
    0 < compactDenominatorLower g η := by
  unfold compactDenominatorLower
  split_ifs with hc
  · apply abs_pos.mpr
    intro hd
    apply g.det.ne_zero
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hc, hd]
  · exact mul_pos (abs_pos.mpr hc) hη

theorem compactDenominatorLower_le (g : GL (Fin 2) ℝ) {η : ℝ}
    (z : UpperHalfPlane) (hz : η ≤ z.im) :
    compactDenominatorLower g η ≤ ‖denom g z‖ := by
  unfold compactDenominatorLower
  split_ifs with hc
  · simp [denom, hc, Complex.norm_real, Real.norm_eq_abs]
  · calc
      _ ≤ |g 1 0| * z.im := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = |(denom g z).im| := by
        simp [denom, Complex.mul_im, abs_mul, abs_of_pos z.im_pos]
      _ ≤ _ := Complex.abs_im_le_norm _

theorem compact_affine_bound (a b : ℝ) {B R : ℝ} (hB : 0≤B)
    (ha : |a|≤B) (hb : |b|≤B) (z : ℂ) (hz : ‖z‖≤R) :
    ‖(a:ℂ)*z+b‖ ≤ B*(R+1) := by
  calc
    _ ≤ ‖(a:ℂ)*z‖ + ‖(b:ℂ)‖ := norm_add_le _ _
    _ = |a| * ‖z‖+|b| := by simp [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ B*R+B := add_le_add (mul_le_mul ha hz (norm_nonneg _) hB) hb
    _ = _ := by ring

/-- Explicit bounds for both image coordinates of an actual positive
Möbius matrix on a bounded region separated from the real axis. -/
theorem compact_image_coordinates (g : GL (Fin 2) ℝ) (hg : 0<g.det.val)
    {B R η : ℝ} (hB : 0<B) (hR : 0≤R) (hη : 0<η)
    (hentries : ∀ i j, |g i j|≤B) (z : UpperHalfPlane)
    (hz : ‖(z:ℂ)‖≤R) (hzi : η≤z.im) :
    |(g • z).re| ≤ B*(R+1)/compactDenominatorLower g η ∧
      g.det.val*η/(B*(R+1))^2 ≤ (g • z).im := by
  have hlo := compactDenominatorLower_pos g hη
  have hden := compactDenominatorLower_le g z hzi
  have hn := compact_affine_bound (g 0 0) (g 0 1) hB.le (hentries 0 0) (hentries 0 1) z hz
  have hd := compact_affine_bound (g 1 0) (g 1 1) hB.le (hentries 1 0) (hentries 1 1) z hz
  change ‖num g z‖ ≤ B*(R+1) at hn
  change ‖denom g z‖ ≤ B*(R+1) at hd
  constructor
  · calc
      _ ≤ ‖((g • z : UpperHalfPlane):ℂ)‖ := Complex.abs_re_le_norm _
      _ = ‖num g z‖/‖denom g z‖ := by rw [coe_smul_of_det_pos hg, norm_div]
      _ ≤ _ := div_le_div₀ (by positivity : 0≤B*(R+1)) hn hlo hden
  · rw [im_smul_eq_div_normSq, abs_of_pos hg]
    have hs : Complex.normSq (denom g z) ≤ (B*(R+1))^2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hd 2
    exact div_le_div₀ (mul_nonneg hg.le z.im_pos.le)
      (mul_le_mul_of_nonneg_left hzi hg.le) (normSq_denom_pos g z.im_ne_zero) hs

#print axioms compactDenominatorLower_pos
#print axioms compactDenominatorLower_le
#print axioms compact_image_coordinates

end QuantitativeHolomorphic
