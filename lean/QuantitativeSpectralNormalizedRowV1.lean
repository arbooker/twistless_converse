module

public import QuantitativeSpectralTriangularAssemblyV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralNormalizedRow

variable {A : Type*} [CStarAlgebra A]
  (R B : A) (hR : IsStarProjection R) (c : ℝ)

/-- An invertible extension of the compressed Gram operator, scaled so
that coercivity on the cut gives the global lower bound one. -/
def augmentedGram : A := (c^2)⁻¹ • (R*star B*B*R) + (1-R)

/-- The explicit normalized left inverse used to build a triangular row. -/
def normalizer : A := c⁻¹ • (Ring.inverse (augmentedGram R B c)*R*star B)

include hR in
theorem augmentedGram_mul_projection : augmentedGram R B c*R = (c^2)⁻¹ • (R*star B*B*R) := by
  unfold augmentedGram
  rw [add_mul, smul_mul_assoc, mul_assoc (R*star B*B), hR.isIdempotentElem.eq,
    sub_mul, one_mul, hR.isIdempotentElem.eq, sub_self, add_zero]

include hR in
theorem projection_mul_augmentedGram : R*augmentedGram R B c = (c^2)⁻¹ • (R*star B*B*R) := by
  unfold augmentedGram
  rw [mul_add, mul_smul_comm, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    hR.isIdempotentElem.eq, mul_sub, mul_one, hR.isIdempotentElem.eq, sub_self, add_zero]

variable [PartialOrder A] [StarOrderedRing A]

theorem augmentedGram_ge_one (hc : 0 < c)
    (hcoercive : c^2 • R ≤ R*star B*B*R) : 1 ≤ augmentedGram R B c := by
  have hh := smul_le_smul_of_nonneg_left hcoercive (inv_nonneg.mpr (sq_nonneg c))
  rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hc.ne'), one_smul] at hh
  simpa [augmentedGram, add_sub_cancel, add_comm] using add_le_add_right hh (1-R)

theorem augmentedGram_strictlyPositive (hc : 0 < c)
    (hcoercive : c^2 • R ≤ R*star B*B*R) : IsStrictlyPositive (augmentedGram R B c) :=
  IsStrictlyPositive.of_le isStrictlyPositive_one (augmentedGram_ge_one R B c hc hcoercive)

include hR in
theorem inverse_commutes_projection (hc : 0 < c)
    (hcoercive : c^2 • R ≤ R*star B*B*R) :
    Ring.inverse (augmentedGram R B c)*R = R*Ring.inverse (augmentedGram R B c) := by
  have hu := (augmentedGram_strictlyPositive R B c hc hcoercive).isUnit
  apply (Ring.inverse_mul_eq_iff_eq_mul _ _ _ hu).mpr
  rw [← mul_assoc, augmentedGram_mul_projection R B hR c,
    ← projection_mul_augmentedGram R B hR c, mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]

include hR in
theorem normalizer_left_supported (hc : 0 < c)
    (hcoercive : c^2 • R ≤ R*star B*B*R) : R*normalizer R B c = normalizer R B c := by
  unfold normalizer
  rw [mul_smul_comm, ← mul_assoc, ← mul_assoc,
    ← inverse_commutes_projection R B hR c hc hcoercive,
    mul_assoc _ R R, hR.isIdempotentElem.eq]

include hR in
/-- Exact diagonal normalization; no estimate or approximate inverse is
introduced at a deflation step. -/
theorem normalized_diagonal (hc : 0 < c)
    (hcoercive : c^2 • R ≤ R*star B*B*R) : normalizer R B c*B*R = c • R := by
  have hu := (augmentedGram_strictlyPositive R B c hc hcoercive).isUnit
  have he : R*star B*B*R = c^2 • (augmentedGram R B c*R) := by
    rw [augmentedGram_mul_projection R B hR c, smul_smul,
      mul_inv_cancel₀ (pow_ne_zero 2 hc.ne'), one_smul]
  unfold normalizer
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [mul_assoc _ R (star B), mul_assoc _ (R*star B) B, mul_assoc _ (R*star B*B) R,
    he, mul_smul_comm, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul, smul_smul]
  congr 1
  field_simp

omit [PartialOrder A] [StarOrderedRing A] in
/-- The orthogonal-image zero from a spectral cut passes exactly through
the normalized inverse row. -/
theorem normalized_off_diagonal (P : A)
    (hzero : R*star B*B*P = 0) : normalizer R B c*B*P = 0 := by
  unfold normalizer
  rw [smul_mul_assoc, smul_mul_assoc, mul_assoc _ R (star B),
    mul_assoc _ (R*star B) B, mul_assoc _ (R*star B*B) P, hzero, mul_zero, smul_zero]

include hR in
theorem normalizer_range_gram (hc : 0 < c)
    (hcoercive : c^2 • R ≤ R*star B*B*R) :
    normalizer R B c*star (normalizer R B c) = R*Ring.inverse (augmentedGram R B c) := by
  have hp := augmentedGram_strictlyPositive R B c hc hcoercive
  have hself := (IsSelfAdjoint.of_nonneg hp.nonneg).ringInverse.star_eq
  calc
    normalizer R B c*star (normalizer R B c) =
        (c^2)⁻¹ • (Ring.inverse (augmentedGram R B c)*(R*star B*B*R)*
          Ring.inverse (augmentedGram R B c)) := by
      simp only [normalizer, star_smul, star_mul, star_star, hR.isSelfAdjoint.star_eq,
        hself, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc,
        pow_two, mul_inv_rev]
    _ = Ring.inverse (augmentedGram R B c)*(augmentedGram R B c*R)*
        Ring.inverse (augmentedGram R B c) := by
      rw [augmentedGram_mul_projection R B hR c, mul_smul_comm, smul_mul_assoc]
    _ = R*Ring.inverse (augmentedGram R B c) := by
      rw [← mul_assoc, Ring.inverse_mul_cancel _ hp.isUnit, one_mul]

include hR in
/-- Coercivity of the removed cut makes the explicit normalizer a contraction.
Thus normalizing the diagonal costs no factor depending on the packet size. -/
theorem normalizer_norm_le_one (hc : 0 < c)
    (hcoercive : c^2 • R ≤ R*star B*B*R) : ‖normalizer R B c‖ ≤ 1 := by
  have hb : Ring.inverse (augmentedGram R B c) ≤ 1 := by
    have hh := CStarAlgebra.ringInverse_le_ringInverse
      (augmentedGram_ge_one R B c hc hcoercive) isStrictlyPositive_one
    simpa only [Ring.inverse_one] using hh
  have hconj := star_left_conjugate_le_conjugate hb R
  simp only [hR.isSelfAdjoint.star_eq, mul_one, hR.isIdempotentElem.eq] at hconj
  have he : R*Ring.inverse (augmentedGram R B c)*R =
      R*Ring.inverse (augmentedGram R B c) := by
    rw [mul_assoc, inverse_commutes_projection R B hR c hc hcoercive,
      ← mul_assoc, hR.isIdempotentElem.eq]
  rw [he] at hconj
  have hgram : normalizer R B c*star (normalizer R B c) ≤ 1 := by
    rw [normalizer_range_gram R B hR c hc hcoercive]
    exact hconj.trans hR.le_one
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (mul_star_self_nonneg (normalizer R B c))).mpr hgram
  rw [CStarRing.norm_self_mul_star] at hn
  nlinarith [norm_nonneg (normalizer R B c)]

#print axioms augmentedGram_strictlyPositive
#print axioms normalizer_left_supported
#print axioms normalized_diagonal
#print axioms normalized_off_diagonal
#print axioms normalizer_range_gram
#print axioms normalizer_norm_le_one

end QuantitativeSpectralNormalizedRow
