module

public import AsymptoticCongruenceWeightV1
public import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix UpperHalfPlane
open AsymptoticCongruenceWeight AsymptoticCompactBranch AsymptoticMassTransport
open scoped MatrixGroups

namespace QuantitativeMaass

/-- An elementary denominator bound uniform on the standard cusp strip.
The nonzero integral lower-left entry supplies the lower bound on its
absolute value. -/
theorem cusp_row_denominator_lower (c d x y : ℝ) (hc : 1≤ |c|)
    (hx : |x|≤1/2) (hy : 1/2≤y) :
    |c| *y*(1+|d|)≤4*((c*x+d)^2+(c*y)^2) := by
  have hu : 1/2≤ |c| *y := by
    calc
      (1:ℝ)/2≤y := hy
      _=1*y := (one_mul y).symm
      _≤ |c| *y := mul_le_mul_of_nonneg_right hc (by linarith)
  have hcu : |c|≤2*(|c| *y) := by
    nlinarith [mul_nonneg (abs_nonneg c) (show 0≤2*y-1 by linarith)]
  have hd : |d|≤ |c*x+d|+|c| *|x| := by
    calc
      |d|=|(c*x+d)-(c*x)| := by congr 1; ring
      _≤ |c*x+d|+|c*x| := abs_sub _ _
      _=|c*x+d|+|c| *|x| := by rw [abs_mul]
  have hdx : |c| *|x|≤ |c|/2 := by nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg c)]
  have hd' : |d|≤ |c*x+d|+|c| *y := by linarith
  have hmul := mul_le_mul_of_nonneg_left hd' (show 0≤ |c| *y by linarith)
  have hsq := sq_nonneg (|c| *y-|c*x+d|)
  have hsmall := mul_nonneg (show 0≤ |c| *y-1/2 by linarith) (show 0≤ |c| *y by linarith)
  nlinarith [sq_abs c,sq_abs (c*x+d),sq_nonneg (c*x+d),sq_nonneg (c*y)]

/-- The nonparabolic row contribution is dominated by a product of two
summable integer tails, independently of cusp height. -/
theorem cusp_row_height_square_bound (c d x y : ℝ) (hc : 1≤ |c|)
    (hx : |x|≤1/2) (hy : 1/2≤y) :
    (y/((c*x+d)^2+(c*y)^2))^2≤16/(c^2*(1+|d|)^2) := by
  have hy0 : 0<y := by linarith
  have hc0 : 0< |c| := lt_of_lt_of_le zero_lt_one hc
  have ha : 0< |c| *(1+|d|) := mul_pos hc0 (by positivity)
  have hq : 0<(c*x+d)^2+(c*y)^2 := by
    have hn : c*y≠0 := mul_ne_zero (abs_pos.mp hc0) hy0.ne'
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hn)
  have hb : y/((c*x+d)^2+(c*y)^2)≤4/(|c| *(1+|d|)) := by
    apply (div_le_div_iff₀ hq ha).mpr
    nlinarith [cusp_row_denominator_lower c d x y hc hx hy]
  have hs := pow_le_pow_left₀ (div_nonneg hy0.le hq.le) hb 2
  simpa only [div_pow,mul_pow,sq_abs,show (4:ℝ)^2=16 by norm_num] using hs

#print axioms cusp_row_denominator_lower
#print axioms cusp_row_height_square_bound

end QuantitativeMaass
