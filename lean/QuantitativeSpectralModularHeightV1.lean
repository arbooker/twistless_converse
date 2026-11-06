module

public import QuantitativeHolomorphicWordGeometryV1
public import AsymptoticCompactBranchV1
public import Mathlib.NumberTheory.Modular

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralModularHeight

open Matrix UpperHalfPlane AsymptoticCompactBranch QuantitativeHolomorphic
open scoped MatrixGroups

/-- A fixed integral modular branch maps a truncated reduction strip to
height bounded below by an explicit inverse polynomial in the truncation.
The matrix bound can be applied uniformly to finitely many actual coset
representatives or to a word with the proved entry-height bound. -/
theorem modular_height_lower (g : SL(2,ℤ)) {B a H : ℝ}
    (hB : 0 ≤ B) (hg : MatrixEntryBound g.val B) (_ha : 0 < a)
    (z : ℍ) (hre : |z.re| ≤ 1) (hlo : a ≤ z.im) (hhi : z.im ≤ H) :
    a/(B^2*(H+2)^2) ≤ (g • z).im := by
  have hd : ‖denom g z‖ ≤ B*(H+2) := by
    simpa only [ModularGroup.denom_apply] using strip_matrix_denominator_bound hB hg z hre hhi
  have hpos : 0 < ‖denom g z‖ := norm_pos_iff.mpr (denom_ne_zero_of_im g z.im_ne_zero)
  have hbpos : 0 < B*(H+2) := hpos.trans_le hd
  have hsq : Complex.normSq (denom g z) ≤ B^2*(H+2)^2 := by
    rw [Complex.normSq_eq_norm_sq]
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) hbpos.le).mpr hd
  have hden : 0 < Complex.normSq (denom g z) := normSq_denom_pos g z.im_ne_zero
  rw [ModularGroup.im_smul_eq_div_normSq]
  calc
    a/(B^2*(H+2)^2) ≤ z.im/(B^2*(H+2)^2) :=
      div_le_div_of_nonneg_right hlo (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ z.im/Complex.normSq (denom g z) :=
      div_le_div_of_nonneg_left z.im_pos.le hden hsq

/-- Removing the actual cap weight on a positive-height region has this
explicit operator-multiplier bound. -/
theorem cap_inverse_of_height {ε eta : ℝ} (hε : 0 < ε) (heta : 0 < eta)
    (t : ℕ) (z : ℍ) (hz : eta ≤ z.im) :
    (cap ε t z)⁻¹ ≤ (max 1 (ε/eta))^t := by
  by_cases hhigh : ε ≤ z.im
  · rw [cap, min_eq_right ((one_le_div hε).mpr hhigh), one_pow, inv_one]
    exact one_le_pow₀ (le_max_left _ _)
  · have hlow : z.im ≤ ε := (lt_of_not_ge hhigh).le
    rw [cap, min_eq_left ((div_le_one hε).mpr hlow), ← inv_pow, inv_div]
    apply pow_le_pow_left₀ (div_nonneg hε.le z.im_pos.le)
    exact (div_le_div_of_nonneg_left hε.le heta hz).trans (le_max_right _ _)

/-- Polynomial unweighting bound on an actual integral image of the
truncated strip. The fixed matrix entries and cap scale are exposed. -/
theorem cap_inverse_modular (g : SL(2,ℤ)) {B a H ε : ℝ}
    (hB : 0 < B) (hg : MatrixEntryBound g.val B) (ha : 0 < a) (hε : 0 < ε)
    (t : ℕ) (z : ℍ) (hre : |z.re| ≤ 1) (hlo : a ≤ z.im) (hhi : z.im ≤ H) :
    (cap ε t (g • z))⁻¹ ≤ (max 1 ((ε/a)*B^2*(H+2)^2))^t := by
  have hH : 0 < H+2 := by linarith [z.im_pos]
  have hlow := modular_height_lower g hB.le hg ha z hre hlo hhi
  have h := cap_inverse_of_height hε
    (div_pos ha (mul_pos (sq_pos_of_pos hB) (sq_pos_of_pos hH))) t (g • z) hlow
  convert h using 1
  congr 2
  field_simp

#print axioms modular_height_lower
#print axioms cap_inverse_of_height
#print axioms cap_inverse_modular

end QuantitativeSpectralModularHeight
