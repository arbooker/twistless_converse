module

public import QuantitativeSpectralExceptionalFundamentalWitnessV1
public import QuantitativeSpectralObservabilityPolynomialV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalGeometry

open UpperHalfPlane Set AsymptoticCompactBranch
open AsymptoticCongruenceLabels QuantitativeSpectralObservability
open QuantitativeSpectralModularHeight
open scoped MatrixGroups

/-- The fixed matrix constant includes its actual determinant. -/
def heightConstant (g : GL (Fin 2) ℝ) : ℝ :=
  4*(1+|g 1 0|+|g 1 1|)^2/ |g.det.val|

theorem heightConstant_pos (g : GL (Fin 2) ℝ) : 0<heightConstant g := by
  have hd : 0 < |g.det.val| := abs_pos.mpr g.det.ne_zero
  unfold heightConstant
  positivity

/-- A literal real Möbius matrix has an explicit reciprocal-height bound
on the overlapping rectangle, with quadratic cutoff dependence. -/
theorem wideBox_cap_inverse (g : GL (Fin 2) ℝ) (H : ℝ) {ε : ℝ}
    (hε : 0<ε) (t : ℕ) (z : ℍ) (hz : z∈wideBox H) :
    (cap ε t (g • z))⁻¹ ≤ (max 1 (ε*heightConstant g*(H+3)^2))^t := by
  let B : ℝ := 1+|g 1 0|+|g 1 1|
  have hB : 0<B := by dsimp [B]; positivity
  have hH : 0<H+3 := by linarith [hz.2.2.1,hz.2.2.2]
  have hb0 : |g 1 0| ≤ B := by dsimp [B]; linarith [abs_nonneg (g 1 1)]
  have hb1 : |g 1 1| ≤ B := by dsimp [B]; linarith [abs_nonneg (g 1 0)]
  have hn : ‖(z:ℂ)‖≤H+2 := by
    have hh := Complex.norm_le_abs_re_add_abs_im (z:ℂ)
    change ‖(z:ℂ)‖≤|z.re|+|z.im| at hh
    rw [abs_of_pos z.im_pos] at hh
    have hr : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith [hz.1],hz.2.1⟩
    linarith [hz.2.2.2]
  have hd : ‖denom g z‖≤B*(H+3) := by
    calc
      _ ≤ ‖(g 1 0:ℂ)*(z:ℂ)‖+‖(g 1 1:ℂ)‖ := norm_add_le _ _
      _ = |g 1 0| * ‖(z:ℂ)‖+|g 1 1| := by rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
      _ ≤ B*(H+2)+B := add_le_add (mul_le_mul hb0 hn (norm_nonneg _) hB.le) hb1
      _ = _ := by ring
  have hsq : Complex.normSq (denom g z)≤B^2*(H+3)^2 := by
    rw [Complex.normSq_eq_norm_sq]
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (mul_pos hB hH).le).mpr hd
  have hdet : 0 < |g.det.val| := abs_pos.mpr g.det.ne_zero
  have hlow : (|g.det.val| / 4)/(B^2*(H+3)^2)≤(g • z).im := by
    rw [im_smul_eq_div_normSq]
    exact (div_le_div_of_nonneg_right (by nlinarith [hz.2.2.1] : |g.det.val| / 4≤|g.det.val| * z.im)
      (by positivity)).trans (div_le_div_of_nonneg_left (by positivity)
        (normSq_denom_pos g z.im_ne_zero) hsq)
  have hh := cap_inverse_of_height hε (show 0<(|g.det.val| / 4)/(B^2*(H+3)^2) by positivity)
    t (g • z) hlow
  convert hh using 1
  congr 2
  dsimp [heightConstant,B]
  field_simp

#print axioms wideBox_cap_inverse

end QuantitativeSpectralExceptionalGeometry
