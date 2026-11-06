module

public import QuantitativeEulerEndpointImageV1

set_option autoImplicit false
set_option maxHeartbeats 900000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeHolomorphic QuantitativeEulerDiamondDecode
open AsymptoticRationalBranches AsymptoticRationalFreeness
open scoped Classical

/-- A numerator or denominator bound on a rectangle of arbitrary width. -/
theorem wide_integer_row_bound {M : IntegerMatrix2} {B R H : ℝ}
    (hB : 0≤B) (hb : MatrixEntryBound M B) (i : Fin 2) (z : ℍ)
    (hre : |z.re|≤R) (him : z.im≤H) :
    ‖(M i 0 : ℂ)*(z : ℂ)+M i 1‖≤B*(H+R+1) := by
  have hz : ‖(z : ℂ)‖≤H+R := by
    have hh := Complex.norm_le_abs_re_add_abs_im (z : ℂ)
    rw [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,abs_of_pos z.im_pos] at hh
    linarith
  calc
    _ ≤ ‖(M i 0 : ℂ)*(z : ℂ)‖+‖(M i 1 : ℂ)‖ := norm_add_le _ _
    _ = |(M i 0 : ℝ)| *‖(z : ℂ)‖+|(M i 1 : ℝ)| := by
      rw [norm_mul,Complex.norm_intCast,Complex.norm_intCast]
    _ ≤ B*(H+R)+B := add_le_add
      (mul_le_mul (hb i 0) hz (norm_nonneg _) hB) (hb i 1)
    _ = _ := by ring

def wideDistortion (B R H : ℝ) : ℝ := max 1 ((B*(H+R+1))^2)

theorem wideDistortion_pos (B R H : ℝ) : 0<wideDistortion B R H :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- The weight distortion is independent of the lower height and epsilon,
while retaining the source width explicitly. -/
theorem wide_integer_height_distortion {g : G} {M : IntegerMatrix2} {B R H : ℝ}
    (hM : IntegerAction g M) (hB : 0≤B) (hb : MatrixEntryBound M B)
    (z : ℍ) (hre : |z.re|≤R) (him : z.im≤H) :
    z.im≤wideDistortion B R H*(g • z).im := by
  have hd := QuantitativeArithmetic.integer_matrix_denominator_ne_zero M hM.1 z
  have hn := Complex.normSq_pos.mpr hd
  have hbound := wide_integer_row_bound hB hb 1 z hre him
  have hs : Complex.normSq ((M 1 0 : ℂ)*(z : ℂ)+M 1 1)≤wideDistortion B R H := by
    rw [Complex.normSq_eq_norm_sq]
    exact (pow_le_pow_left₀ (norm_nonneg _) hbound 2).trans (le_max_right _ _)
  have he := (eq_div_iff hn.ne').mp (hM.im_formula z)
  have hdet := hM.det_one_le
  nlinarith [mul_le_mul_of_nonneg_right hs (g • z).im_pos.le,
    mul_le_mul_of_nonneg_right hdet z.im_pos.le]

theorem wide_integer_image_norm {g : G} {M : IntegerMatrix2} {B R Y H : ℝ}
    (hM : IntegerAction g M) (hB : 0≤B) (hb : MatrixEntryBound M B)
    (hY : 0<Y) (z : ℍ) (hre : |z.re|≤R) (hlo : Y≤z.im) (him : z.im≤H) :
    ‖((g • z : ℍ) : ℂ)‖≤B*(H+R+1)/(min 1 Y) := by
  have hn := wide_integer_row_bound hB hb 0 z hre him
  have hd : min 1 Y≤‖(M 1 0 : ℂ)*(z : ℂ)+M 1 1‖ :=
    (min_le_min_left 1 hlo).trans (integer_denominator_norm_lower M hM.1 z)
  have hm : 0<min 1 Y := lt_min zero_lt_one hY
  have hnum : 0≤B*(H+R+1) := (norm_nonneg _).trans hn
  rw [hM.2 z,norm_div]
  exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left hnum hm hd)

/-- A common image rectangle for arbitrary source width, with explicit
polynomial and reciprocal-polynomial endpoints. -/
def wideImageRegion (B R Y H : ℝ) : Set ℍ :=
  observationRectangle (B*(H+R+1)/min 1 Y) (Y/wideDistortion B R H)
    (B*(H+R+1)/min 1 Y)

theorem wideImageRegion_compact (B R H : ℝ) {Y : ℝ} (hY : 0<Y) :
    IsCompact (wideImageRegion B R Y H) :=
  observationRectangle_compact _ _ (div_pos hY (wideDistortion_pos B R H))

theorem wide_integer_image_mem {g : G} {M : IntegerMatrix2} {B R Y H : ℝ}
    (hM : IntegerAction g M) (hB : 0≤B) (hb : MatrixEntryBound M B)
    (hY : 0<Y) (z : ℍ) (hre : |z.re|≤R) (hlo : Y≤z.im) (him : z.im≤H) :
    g • z∈wideImageRegion B R Y H := by
  have hn := wide_integer_image_norm hM hB hb hY z hre hlo him
  refine ⟨(Complex.abs_re_le_norm ((g • z : ℍ) : ℂ)).trans hn,?_,?_⟩
  · apply (div_le_iff₀ (wideDistortion_pos B R H)).2
    simpa only [mul_comm] using hlo.trans (wide_integer_height_distortion hM hB hb z hre him)
  · exact (le_abs_self _).trans ((Complex.abs_im_le_norm ((g • z : ℍ) : ℂ)).trans hn)

theorem branchImage_subset_wide (b : AsymptoticRegularBranchFamily.Branch)
    {M : IntegerMatrix2} {B R Y H : ℝ}
    (hM : IntegerAction (ofMatrix b.matrix b.positive) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hY : 0<Y)
    {s : Set ℍ} (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im)
    (him : ∀ z∈s, z.im≤H) : branchImage b s⊆wideImageRegion B R Y H := by
  rintro _ ⟨z,hz,rfl⟩
  exact wide_integer_image_mem hM hB hb hY z (hre z hz) (hlo z hz) (him z hz)

theorem wideDistortion_unit (B H : ℝ) : wideDistortion B 1 H=integerCompactDistortion B H := by
  unfold wideDistortion integerCompactDistortion
  congr 2; ring

theorem wideImageRegion_unit (B Y H : ℝ) : wideImageRegion B 1 Y H=commonImageRegion B Y H := by
  unfold wideImageRegion commonImageRegion
  rw [wideDistortion_unit]
  congr 1 <;> congr 1 <;> ring

#print axioms wide_integer_row_bound
#print axioms wide_integer_height_distortion
#print axioms wide_integer_image_norm
#print axioms wideImageRegion_compact
#print axioms branchImage_subset_wide
#print axioms wideImageRegion_unit
end QuantitativeEulerEndpointPrepared
