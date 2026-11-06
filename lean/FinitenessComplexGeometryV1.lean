module

public import FinitenessAnalyticReconstructionV1
public import FinitenessWindowGainV1

@[expose] public section

namespace FinitenessComplexGeometry

noncomputable def denominator (L : ℝ) (z : ℂ) : ℝ := L * (z.re^2 + z.im^2)

theorem denominator_pos {L : ℝ} {z : ℂ} (hL : 0 < L) (hz : 0 < z.im) :
    0 < denominator L z := by
  exact mul_pos hL (by nlinarith [sq_nonneg z.re])

theorem reflected_im {L : ℝ} {z : ℂ} (hL : 0 < L) (hz : 0 < z.im) :
    (-1 / ((L : ℂ) * z)).im = z.im / denominator L z := by
  have hn : z.re^2 + z.im^2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg z.re])
  simp only [neg_div, one_div, Complex.neg_im, Complex.inv_im,
    Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, Complex.normSq_apply, denominator]
  field_simp

theorem reflected_im_pos {L : ℝ} {z : ℂ} (hL : 0 < L) (hz : 0 < z.im) :
    0 < (-1 / ((L : ℂ) * z)).im := by
  rw [reflected_im hL hz]
  exact div_pos hz (denominator_pos hL hz)

theorem automorphy_norm {L : ℝ} (hL : 0 ≤ L) (z χ : ℂ) (hχ : ‖χ‖ = 1) (m : ℕ) :
    ‖χ / (((Real.sqrt L : ℝ) : ℂ) * z)^(2*m)‖ =
      1 / (denominator L z)^m := by
  have hs : ‖((Real.sqrt L : ℝ) : ℂ) * z‖^2 = denominator L z := by
    rw [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal,
      ← sq, Real.sq_sqrt hL, Complex.normSq_apply]
    simp only [denominator, sq]
  rw [norm_div, hχ, norm_pow, pow_mul, hs]

/-- Real translations do not affect any of the reflected heights. -/
theorem translated_reflected_im {L : ℝ} {z : ℂ} (hL : 0 < L) (hz : 0 < z.im)
    (a : ℝ) : (-1 / ((L : ℂ) * z) + (a : ℂ)).im = z.im / denominator L z := by
  simp only [Complex.add_im, Complex.ofReal_im, add_zero, reflected_im hL hz]

#print axioms reflected_im
#print axioms automorphy_norm

end FinitenessComplexGeometry
