module

public import QuantitativeHolomorphicCompactDataV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane

/-- Integrality gives a uniform denominator lower bound on a retained
strip: the lower row has either a nonzero integer first entry or a nonzero
integer second entry. -/
theorem integer_denominator_norm_lower (M : IntegerMatrix2) (hM : M.det≠0)
    (z : UpperHalfPlane) : min 1 z.im ≤ ‖(M 1 0:ℂ)*(z:ℂ)+M 1 1‖ := by
  by_cases hc : M 1 0=0
  · have hd : M 1 1≠0 := by
      intro hd
      apply hM
      simp [Matrix.det_fin_two,hc,hd]
    have hh : (1:ℝ)≤|(M 1 1:ℝ)| := by exact_mod_cast Int.one_le_abs hd
    simpa [hc,Complex.norm_intCast] using (min_le_left 1 z.im).trans hh
  · have hh : (1:ℝ)≤|(M 1 0:ℝ)| := by exact_mod_cast Int.one_le_abs hc
    have hi := Complex.abs_im_le_norm ((M 1 0:ℂ)*(z:ℂ)+M 1 1)
    have he : |(((M 1 0:ℂ)*(z:ℂ)+M 1 1).im)|=|(M 1 0:ℝ)| *z.im := by
      simp [Complex.mul_im,abs_mul,abs_of_pos z.im_pos]
    rw [he] at hi
    exact (min_le_right 1 z.im).trans ((by nlinarith [z.im_pos] : z.im≤|(M 1 0:ℝ)| *z.im).trans hi)

/-- The usual imaginary-part transformation law follows from the literal
integer Möbius representative. -/
theorem IntegerAction.im_formula {g : AsymptoticRationalGroup.Group} {M : IntegerMatrix2}
    (hM : IntegerAction g M) (z : UpperHalfPlane) :
    (g • z).im = (M.det:ℝ)*z.im / Complex.normSq ((M 1 0:ℂ)*(z:ℂ)+M 1 1) := by
  have he := congrArg Complex.im (hM.2 z)
  change ((g • z : UpperHalfPlane):ℂ).im = _
  rw [he]
  simp only [Complex.div_im,Complex.add_im,Complex.mul_im,Complex.intCast_re,
    Complex.intCast_im,zero_mul,add_zero,Complex.add_re,Complex.mul_re,sub_zero,
    ← sub_div,Matrix.det_fin_two,Int.cast_sub,Int.cast_mul,UpperHalfPlane.coe_im]
  ring

/-- Positivity of the rational label forces its nonsingular integer
representative to have positive integral determinant. -/
theorem IntegerAction.det_one_le {g : AsymptoticRationalGroup.Group} {M : IntegerMatrix2}
    (hM : IntegerAction g M) : (1:ℝ)≤M.det := by
  let z : UpperHalfPlane := ⟨Complex.I,by norm_num⟩
  have hd := QuantitativeArithmetic.integer_matrix_denominator_ne_zero M hM.1 z
  have hn := Complex.normSq_pos.mpr hd
  have he := (eq_div_iff hn.ne').mp (hM.im_formula z)
  have hp : 0<(M.det:ℝ) := by
    have hh := mul_pos (g • z).im_pos hn
    rw [he] at hh
    exact (mul_pos_iff_of_pos_right z.im_pos).mp hh
  have hp' : 0<M.det := by exact_mod_cast hp
  exact_mod_cast (show (1:ℤ)≤M.det by omega)

/-- Explicit denominator distortion for a label with height B on the unit
strip up to height H. This is the quantitative input for the capped weight
ratio, independent of any compactness-selected constants. -/
theorem IntegerAction.height_distortion {g : AsymptoticRationalGroup.Group}
    {M : IntegerMatrix2} {B H : ℝ} (hM : IntegerAction g M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (z : UpperHalfPlane)
    (hre : |z.re|≤1) (him : z.im≤H) :
    z.im≤(B*(H+2))^2*(g • z).im := by
  have hd := QuantitativeArithmetic.integer_matrix_denominator_ne_zero M hM.1 z
  have hn := Complex.normSq_pos.mpr hd
  have hbound := strip_matrix_denominator_bound hB hb z hre him
  have hs : Complex.normSq ((M 1 0:ℂ)*(z:ℂ)+M 1 1)≤(B*(H+2))^2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have he := (eq_div_iff hn.ne').mp (hM.im_formula z)
  have hdet := hM.det_one_le
  nlinarith [mul_le_mul_of_nonneg_right hs (g • z).im_pos.le,
    mul_le_mul_of_nonneg_right hdet z.im_pos.le]

/-- Explicit image-coordinate bound on a retained unit rectangle. This
controls the integer fold interval by matrix height and the lower cutoff. -/
theorem IntegerAction.image_re_bound {g : AsymptoticRationalGroup.Group}
    {M : IntegerMatrix2} {B Y H : ℝ} (hM : IntegerAction g M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hY : 0<Y) (z : UpperHalfPlane)
    (hre : |z.re|≤1) (hlo : Y≤z.im) (him : z.im≤H) :
    |(g • z).re|≤B*(H+2)/(min 1 Y) := by
  have hz : ‖(z:ℂ)‖≤H+1 := by
    have hh := Complex.norm_le_abs_re_add_abs_im (z:ℂ)
    rw [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,abs_of_pos z.im_pos] at hh
    linarith
  have hn : ‖(M 0 0:ℂ)*(z:ℂ)+M 0 1‖≤B*(H+2) := by
    calc
      _ ≤ ‖(M 0 0:ℂ)*(z:ℂ)‖+‖(M 0 1:ℂ)‖ := norm_add_le _ _
      _ = |(M 0 0:ℝ)| *‖(z:ℂ)‖+|(M 0 1:ℝ)| := by
        rw [norm_mul,Complex.norm_intCast,Complex.norm_intCast]
      _ ≤ B*(H+1)+B := add_le_add
        (mul_le_mul (hb 0 0) hz (norm_nonneg _) hB) (hb 0 1)
      _ = _ := by ring
  have hd : min 1 Y≤‖(M 1 0:ℂ)*(z:ℂ)+M 1 1‖ :=
    (min_le_min_left 1 hlo).trans (integer_denominator_norm_lower M hM.1 z)
  have hm : 0<min 1 Y := lt_min zero_lt_one hY
  have hnum : 0≤B*(H+2) := (norm_nonneg _).trans hn
  have he : ‖((g • z:UpperHalfPlane):ℂ)‖≤B*(H+2)/(min 1 Y) := by
    rw [hM.2 z,norm_div]
    exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left hnum hm hd)
  exact (Complex.abs_re_le_norm ((g • z:UpperHalfPlane):ℂ)).trans he

#print axioms integer_denominator_norm_lower
#print axioms IntegerAction.im_formula
#print axioms IntegerAction.det_one_le
#print axioms IntegerAction.height_distortion
#print axioms IntegerAction.image_re_bound

end QuantitativeHolomorphic
