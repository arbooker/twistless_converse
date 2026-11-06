module

public import QuantitativeSpectralCoverUnweightV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralModularCoordinate

open Matrix UpperHalfPlane QuantitativeHolomorphic
open QuantitativeSpectralCoverUnweight QuantitativeSpectralCongruenceCover
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped MatrixGroups

/-- Integral matrices cannot have an arbitrarily small denominator on
a fixed positive-height strip. The triangular case uses determinant one. -/
theorem denom_lower (g : SL(2,ℤ)) (z : ℍ) (hz : (1:ℝ)/4 ≤ z.im) :
    (1:ℝ)/4 ≤ ‖denom g z‖ := by
  by_cases hc : g 1 0=0
  · have hd : g 0 0*g 1 1=1 := by
      have h := g.property
      rw [Matrix.det_fin_two,hc,mul_zero,sub_zero] at h
      exact h
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hd with ⟨_,hd⟩ | ⟨_,hd⟩
    · norm_num [ModularGroup.denom_apply,hc,hd]
    · norm_num [ModularGroup.denom_apply,hc,hd]
  · have hc' : (1:ℝ) ≤ |(g 1 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hc
    have hi := Complex.abs_im_le_norm (denom g z)
    have he : (denom g z).im = (g 1 0 : ℝ)*z.im := by
      simp [ModularGroup.denom_apply,Complex.mul_im]
    rw [he,abs_mul,abs_of_pos z.im_pos] at hi
    exact hz.trans ((by nlinarith [z.im_pos] : z.im ≤ |(g 1 0 : ℝ)| *z.im).trans hi)

/-- Polynomial coordinate bound for the literal compact reduction images. -/
theorem modular_norm_upper (g : SL(2,ℤ)) {B H : ℝ} (hB : 0 ≤ B)
    (hg : MatrixEntryBound g.val B) (z : ℍ) (hre : |z.re| ≤ 1)
    (hlo : (1:ℝ)/4 ≤ z.im) (hhi : z.im ≤ H) :
    ‖((g • z : ℍ):ℂ)‖ ≤ 4*B*(H+2) := by
  have hz : ‖(z:ℂ)‖ ≤ H+1 := by
    have h := Complex.norm_le_abs_re_add_abs_im (z:ℂ)
    change ‖(z:ℂ)‖ ≤ |z.re|+|z.im| at h
    rw [abs_of_pos z.im_pos] at h
    linarith
  have hn : ‖(g 0 0 : ℂ)*(z:ℂ)+(g 0 1 : ℂ)‖ ≤ B*(H+2) := by
    calc
      _ ≤ ‖(g 0 0 : ℂ)*(z:ℂ)‖+‖(g 0 1 : ℂ)‖ := norm_add_le _ _
      _ = |(g 0 0 : ℝ)| *‖(z:ℂ)‖+|(g 0 1 : ℝ)| := by
        rw [norm_mul,Complex.norm_intCast,Complex.norm_intCast]
      _ ≤ B*(H+1)+B := add_le_add (mul_le_mul (hg 0 0) hz (norm_nonneg _) hB) (hg 0 1)
      _ = _ := by ring
  rw [ModularGroup.sl_moeb,coe_smul_of_det_pos (by simp)]
  change ‖((g 0 0 : ℂ)*(z:ℂ)+(g 0 1 : ℂ))/denom g z‖ ≤ _
  rw [norm_div]
  have hden := denom_lower g z hlo
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) hden)).mpr
  have hH : 0 ≤ H+2 := by linarith [z.im_pos]
  have hb : 0 ≤ B*(H+2) := mul_nonneg hB hH
  nlinarith

theorem compactCover_re_bound (N : ℕ) (hN : 0 < N) (H : ℝ)
    {z : ℍ} (hz : z ∈ compactCover N H) :
    |z.re| ≤ 4*coverBound N hN*(H+2) := by
  obtain ⟨q,w,hw,rfl⟩ := Set.mem_iUnion.mp hz
  dsimp only at *
  rw [← map_inv, integralLabel_action]
  apply (Complex.abs_re_le_norm _).trans
  exact modular_norm_upper q.out⁻¹ (by linarith [coverBound_one_le N hN])
    (coverBound_entry N hN q) w (abs_le.mpr ⟨by linarith [hw.1],hw.2.1⟩)
    hw.2.2.1 hw.2.2.2

#print axioms compactCover_re_bound

#print axioms denom_lower
#print axioms modular_norm_upper

end QuantitativeSpectralModularCoordinate
