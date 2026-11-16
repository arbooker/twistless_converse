module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- The half-integer resolvent terms of the spherical density. -/
def halfResolventTerm (r : ℝ) (n : ℕ) : ℝ :=
  r / (((n : ℝ) + 1 / 2) ^ 2 + r ^ 2)

theorem halfResolventTerm_summable (r : ℝ) : Summable (halfResolventTerm r) := by
  have h : Summable (fun n : ℕ => 1 / (((n : ℝ) + 1 / 2) ^ 2)) := by
    simpa only [Real.rpow_two, sq_abs] using
      (Real.summable_one_div_nat_add_rpow (1/2) 2).mpr (by norm_num)
  apply Summable.of_norm_bounded (h.mul_left |r|)
  intro n
  have hu : 0 < ((n : ℝ) + 1 / 2) ^ 2 := sq_pos_of_pos (by positivity)
  simp only [halfResolventTerm, Real.norm_eq_abs, abs_div,
    abs_of_pos (add_pos_of_pos_of_nonneg hu (sq_nonneg r)), mul_one_div]
  exact div_le_div_of_nonneg_left (abs_nonneg r) hu (le_add_of_nonneg_right (sq_nonneg r))

/-- Imaginary part of a reciprocal, in real coordinates. -/
theorem reciprocal_real_imaginary (a r : ℝ) :
    (1 / ((a : ℂ) + (r : ℂ) * Complex.I)).im = -r / (a ^ 2 + r ^ 2) := by
  simp [one_div, Complex.inv_im, Complex.normSq_apply, pow_two]

/-- Cotangent on the vertical line through one half is hyperbolic tangent. -/
theorem cot_half_add_imaginary (r : ℝ) :
    Complex.cot ((Real.pi : ℂ) * (1/2 + (r : ℂ) * Complex.I)) =
      -(Real.tanh (Real.pi*r) : ℂ) * Complex.I := by
  have harg : (Real.pi : ℂ) * (1/2 + (r : ℂ) * Complex.I) =
      (Real.pi : ℂ)/2 + ((Real.pi*r : ℝ) : ℂ)*Complex.I := by
    push_cast
    ring
  rw [harg, Complex.cot_eq_cos_div_sin, Complex.cos_add, Complex.sin_add]
  simp only [Complex.cos_pi_div_two, Complex.sin_pi_div_two,
    Complex.cos_mul_I, Complex.sin_mul_I, zero_mul, one_mul]
  rw [Real.tanh_eq_sinh_div_cosh]
  simp only [Complex.ofReal_div, Complex.ofReal_sinh, Complex.ofReal_cosh]
  ring

/-- The reciprocal at one half gives the first summand. -/
theorem halfResolvent_initial_im (r : ℝ) :
    (1 / (1/2 + (r : ℂ) * Complex.I)).im = -halfResolventTerm r 0 := by
  have h := reciprocal_real_imaginary (1/2) r
  simpa only [halfResolventTerm, Nat.cast_zero, zero_add,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, neg_div] using h

/-- The two cotangent summands give consecutive half-integer terms. -/
theorem halfResolvent_cotTerm_im (r : ℝ) (n : ℕ) :
    (cotTerm (1/2 + (r : ℂ)*Complex.I) n).im =
      -halfResolventTerm r n - halfResolventTerm r (n+1) := by
  have hm : (1/2 + (r : ℂ)*Complex.I) - ((n : ℂ)+1) =
      (((-(n : ℝ)-1/2) : ℝ) : ℂ) + (r : ℂ)*Complex.I := by push_cast; ring
  have hp : (1/2 + (r : ℂ)*Complex.I) + ((n : ℂ)+1) =
      ((((n : ℝ)+3/2) : ℝ) : ℂ) + (r : ℂ)*Complex.I := by push_cast; ring
  simp only [cotTerm, Complex.add_im, hm, hp, reciprocal_real_imaginary,
    halfResolventTerm, Nat.cast_add, Nat.cast_one]
  have h1 : (-(n : ℝ)-1/2)^2=((n : ℝ)+1/2)^2 := by ring
  have h2 : ((n : ℝ)+3/2)^2=((n : ℝ)+1+1/2)^2 := by ring
  rw [h1,h2]
  ring

/-- The exact partial fraction expansion, including zero and negative parameters. -/
theorem halfResolvent_tsum (r : ℝ) :
    2 * ∑' n : ℕ, halfResolventTerm r n = Real.pi * Real.tanh (Real.pi*r) := by
  by_cases hr : r=0
  · simp [hr, halfResolventTerm, Real.tanh_eq_sinh_div_cosh]
  have hz : (1/2 + (r : ℂ)*Complex.I) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨m,hm⟩
    have hi := congrArg Complex.im hm
    simp at hi
    exact hr hi.symm
  have hs := halfResolventTerm_summable r
  have ht : Summable (fun n : ℕ => halfResolventTerm r (n+1)) :=
    (summable_nat_add_iff 1).mpr hs
  have h := congrArg Complex.im (cot_series_rep' hz)
  change ((Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*(1/2+(r:ℂ)*Complex.I)) -
    1/(1/2+(r:ℂ)*Complex.I)).im = (∑' n : ℕ, cotTerm (1/2+(r:ℂ)*Complex.I) n).im at h
  rw [Complex.im_tsum (summable_cotTerm hz)] at h
  simp only [Complex.sub_im, cot_half_add_imaginary, halfResolvent_initial_im,
    halfResolvent_cotTerm_im] at h
  have hl : ((Real.pi:ℂ)*(-(Real.tanh (Real.pi*r):ℂ)*Complex.I)).im =
      -Real.pi*Real.tanh (Real.pi*r) := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    ring
  rw [hl, hs.neg.tsum_sub ht, tsum_neg] at h
  have htail := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at htail
  linarith

/-- HasSum form of the expansion used in integral/series interchange. -/
theorem halfResolvent_hasSum (r : ℝ) :
    HasSum (fun n : ℕ => 2 * halfResolventTerm r n)
      (Real.pi * Real.tanh (Real.pi*r)) := by
  simpa only [halfResolvent_tsum] using (halfResolventTerm_summable r).hasSum.mul_left 2

end QuantitativeMaass

#print axioms QuantitativeMaass.halfResolventTerm_summable
#print axioms QuantitativeMaass.reciprocal_real_imaginary
#print axioms QuantitativeMaass.cot_half_add_imaginary
#print axioms QuantitativeMaass.halfResolvent_initial_im
#print axioms QuantitativeMaass.halfResolvent_cotTerm_im
#print axioms QuantitativeMaass.halfResolvent_tsum
#print axioms QuantitativeMaass.halfResolvent_hasSum
