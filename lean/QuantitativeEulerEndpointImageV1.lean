module

public import QuantitativeEulerEndpointOriginalRowsV1
public import QuantitativeEulerEndpointBranchHeightV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeHolomorphic QuantitativeEulerDiamondDecode
open AsymptoticRationalBranches AsymptoticRationalFreeness Set
open scoped Classical

/-- The image norm, not just its real part, obeys the explicit integer
numerator/denominator bound. -/
theorem integer_image_norm_bound {g : G} {M : IntegerMatrix2} {B Y H : ℝ}
    (hM : IntegerAction g M) (hB : 0≤B) (hb : MatrixEntryBound M B)
    (hY : 0<Y) (z : ℍ) (hre : |z.re|≤1) (hlo : Y≤z.im) (him : z.im≤H) :
    ‖((g • z : ℍ) : ℂ)‖≤B*(H+2)/(min 1 Y) := by
  have hz : ‖(z : ℂ)‖≤H+1 := by
    have hh := Complex.norm_le_abs_re_add_abs_im (z : ℂ)
    rw [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,abs_of_pos z.im_pos] at hh
    linarith
  have hn : ‖(M 0 0 : ℂ)*(z : ℂ)+M 0 1‖≤B*(H+2) := by
    calc
      _ ≤ ‖(M 0 0 : ℂ)*(z : ℂ)‖+‖(M 0 1 : ℂ)‖ := norm_add_le _ _
      _ = |(M 0 0 : ℝ)| *‖(z : ℂ)‖+|(M 0 1 : ℝ)| := by
        rw [norm_mul,Complex.norm_intCast,Complex.norm_intCast]
      _ ≤ B*(H+1)+B := add_le_add
        (mul_le_mul (hb 0 0) hz (norm_nonneg _) hB) (hb 0 1)
      _ = _ := by ring
  have hd : min 1 Y≤‖(M 1 0 : ℂ)*(z : ℂ)+M 1 1‖ :=
    (min_le_min_left 1 hlo).trans (integer_denominator_norm_lower M hM.1 z)
  have hm : 0<min 1 Y := lt_min zero_lt_one hY
  have hnum : 0≤B*(H+2) := (norm_nonneg _).trans hn
  rw [hM.2 z,norm_div]
  exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left hnum hm hd)

theorem integer_image_lower_height {g : G} {M : IntegerMatrix2} {B Y H : ℝ}
    (hM : IntegerAction g M) (hB : 0≤B) (hb : MatrixEntryBound M B)
    (z : ℍ) (hre : |z.re|≤1) (hlo : Y≤z.im) (him : z.im≤H) :
    Y/integerCompactDistortion B H≤(g • z).im := by
  have hd : 0 < integerCompactDistortion B H := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply (div_le_iff₀ hd).2
  have hh := hlo.trans (hM.height_distortion hB hb z hre him)
  exact hh.trans (by
    simpa only [integerCompactDistortion,mul_comm] using mul_le_mul_of_nonneg_right
      (le_max_right 1 ((B*(H+2))^2)) (g • z).im_pos.le)

def observationRectangle (R Y H : ℝ) : Set ℍ :=
  {z | |z.re|≤R ∧ Y≤z.im ∧ z.im≤H}

theorem observationRectangle_compact (R H : ℝ) {Y : ℝ} (hY : 0<Y) :
    IsCompact (observationRectangle R Y H) := by
  have he : UpperHalfPlane.coe '' observationRectangle R Y H=
      Complex.measurableEquivRealProd.symm '' (Icc (-R) R ×ˢ Icc Y H) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨(w.re,w.im),⟨abs_le.mp hw.1,hw.2⟩,rfl⟩
    · rintro ⟨⟨x,y⟩,hxy,rfl⟩
      exact ⟨⟨⟨x,y⟩,hY.trans_le hxy.2.1⟩,⟨abs_le.mpr hxy.1,hxy.2⟩,rfl⟩
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff,he]
  exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous

/-- One explicit rectangle containing every image with integral height B.
The lower endpoint is positive; all bounds are polynomial or reciprocal
polynomial expressions in the input geometric parameters. -/
def commonImageRegion (B Y H : ℝ) : Set ℍ :=
  observationRectangle (B*(H+2)/(min 1 Y)) (Y/integerCompactDistortion B H)
    (B*(H+2)/(min 1 Y))

theorem commonImageRegion_compact (B H : ℝ) {Y : ℝ} (hY : 0<Y) :
    IsCompact (commonImageRegion B Y H) :=
  observationRectangle_compact _ _ (div_pos hY (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

theorem integer_image_mem_common {g : G} {M : IntegerMatrix2} {B Y H : ℝ}
    (hM : IntegerAction g M) (hB : 0≤B) (hb : MatrixEntryBound M B)
    (hY : 0<Y) (z : ℍ) (hre : |z.re|≤1) (hlo : Y≤z.im) (him : z.im≤H) :
    g • z∈commonImageRegion B Y H := by
  have hn := integer_image_norm_bound hM hB hb hY z hre hlo him
  refine ⟨(Complex.abs_re_le_norm ((g • z : ℍ) : ℂ)).trans hn,
    integer_image_lower_height hM hB hb z hre hlo him,?_⟩
  exact (le_abs_self _).trans ((Complex.abs_im_le_norm ((g • z : ℍ) : ℂ)).trans hn)

theorem branchImage_subset_common (b : AsymptoticRegularBranchFamily.Branch)
    {M : IntegerMatrix2} {B Y H : ℝ}
    (hM : IntegerAction (ofMatrix b.matrix b.positive) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hY : 0<Y)
    {s : Set ℍ} (hre : ∀ z∈s, |z.re|≤1) (hlo : ∀ z∈s, Y≤z.im)
    (him : ∀ z∈s, z.im≤H) : branchImage b s⊆commonImageRegion B Y H := by
  rintro _ ⟨z,hz,rfl⟩
  exact integer_image_mem_common hM hB hb hY z (hre z hz) (hlo z hz) (him z hz)

#print axioms integer_image_norm_bound
#print axioms integer_image_lower_height
#print axioms commonImageRegion_compact
#print axioms branchImage_subset_common
end QuantitativeEulerEndpointPrepared
