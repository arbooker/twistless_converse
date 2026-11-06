module

public import AsymptoticBergmanDecayV1

set_option autoImplicit false
@[expose] public section

namespace QuantitativeHolomorphic

open UpperHalfPlane AsymptoticBergmanDecay

/-- Exact quantitative identity for the already formalized Bergman base.
This is the starting point for displacement-sublevel estimates. -/
theorem bergman_norm_sq_identity (z u : ℍ) :
    ‖base z u‖ ^ 2 * (‖(z : ℂ) - (u : ℂ)‖ ^ 2 + 4 * z.im * u.im) =
      4 * z.im * u.im := by
  rw [← denominator_square, norm_base, div_pow]
  have hd : ‖(z : ℂ) - star (u : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (denominator_ne_zero z u)
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 hd)]
  have hs := Real.sq_sqrt (mul_nonneg z.im_pos.le u.im_pos.le)
  nlinarith

/-- Uniform kernel control away from the diagonal, with the compact
height dependence explicit. -/
theorem bergman_separated_factor (z u : ℍ) {r H : ℝ}
    (hr : 0 ≤ r) (hH : 0 < H) (hzu : r ≤ ‖(z : ℂ) - (u : ℂ)‖)
    (hheight : z.im * u.im ≤ H ^ 2) :
    ‖base z u‖ ^ 2 * (1 + r ^ 2 / (4 * H ^ 2)) ≤ 1 := by
  have hbase : ‖base z u‖ ^ 2 ≤ 1 := by
    nlinarith [norm_base_le_one z u, norm_nonneg (base z u)]
  have hdist : r ^ 2 ≤ ‖(z : ℂ) - (u : ℂ)‖ ^ 2 :=
    pow_le_pow_left₀ hr hzu 2
  have hm := mul_le_mul_of_nonneg_left hdist (sq_nonneg ‖base z u‖)
  have hh := mul_nonneg (sub_nonneg.mpr hheight) (sub_nonneg.mpr hbase)
  have hid := bergman_norm_sq_identity z u
  have hnum : ‖base z u‖ ^ 2 * (4 * H ^ 2 + r ^ 2) ≤ 4 * H ^ 2 := by
    nlinarith
  have hden : 0 < 4 * H ^ 2 := by positivity
  have heq : 1 + r ^ 2 / (4 * H ^ 2) = (4 * H ^ 2 + r ^ 2) / (4 * H ^ 2) := by
    field_simp
  rw [heq, ← mul_div_assoc]
  exact (div_le_one hden).mpr hnum

/-- Bernoulli gives a uniform polynomial decay bound; unlike pointwise
dominated convergence, this retains the height and displacement constants.
It is not yet the integrated arithmetic finite-branch trace theorem. -/
theorem bergman_even_power_bound (z u : ℍ) {r H : ℝ}
    (hr : 0 ≤ r) (hH : 0 < H) (hzu : r ≤ ‖(z : ℂ) - (u : ℂ)‖)
    (hheight : z.im * u.im ≤ H ^ 2) (n : ℕ) :
    ‖base z u‖ ^ (2 * n) ≤ 1 / (1 + (n : ℝ) * r ^ 2 / (4 * H ^ 2)) := by
  let q := ‖base z u‖ ^ 2
  let a := r ^ 2 / (4 * H ^ 2)
  have hq : 0 ≤ q := sq_nonneg _
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hfactor : q * (1 + a) ≤ 1 := bergman_separated_factor z u hr hH hzu hheight
  have hpow : q ^ n * (1 + a) ^ n ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (mul_nonneg hq (by linarith)) hfactor
  have hbern : 1 + (n : ℝ) * a ≤ (1 + a) ^ n :=
    one_add_mul_le_pow (by linarith : -2 ≤ a) n
  have hm := mul_le_mul_of_nonneg_left hbern (pow_nonneg hq n)
  have hden : 0 < 1 + (n : ℝ) * a := by positivity
  have hh : q ^ n ≤ 1 / (1 + (n : ℝ) * a) :=
    (le_div_iff₀ hden).mpr (hm.trans hpow)
  simpa only [q, a, ← pow_mul, mul_div_assoc] using hh

#print axioms bergman_norm_sq_identity
#print axioms bergman_separated_factor
#print axioms bergman_even_power_bound

end QuantitativeHolomorphic
