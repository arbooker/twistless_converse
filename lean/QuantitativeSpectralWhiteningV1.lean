module

public import QuantitativeSpectralNormalizedRowV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralWhitening

open QuantitativeSpectralNormalizedRow

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A bounded right inverse on a coercive spectral support, constructed using
the adjoint of the already normalized left inverse. Applied to the absolute
value of a rectangular stack, this is its truncated polar whitening map. -/
def whitening (R B : A) (c : ℝ) : A := c⁻¹ • star (normalizer R B c)

theorem whitening_norm_le (R B : A) (hR : IsStarProjection R) {c : ℝ}
    (hc : 0 < c) (hcoercive : c^2 • R ≤ R*star B*B*R) :
    ‖whitening R B c‖ ≤ c⁻¹ := by
  rw [whitening, norm_smul, norm_star, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (normalizer_norm_le_one R B hR c hc hcoercive) (inv_nonneg.mpr hc.le)

theorem whitening_right_inverse (R B : A) (hR : IsStarProjection R)
    (hB : IsSelfAdjoint B) (hBR : B*R=B) {c : ℝ} (hc : 0 < c)
    (hcoercive : c^2 • R ≤ R*star B*B*R) : B*whitening R B c = R := by
  have hd := normalized_diagonal R B hR c hc hcoercive
  rw [mul_assoc, hBR] at hd
  have hds := congrArg star hd
  simp only [star_mul, hB.star_eq, star_smul, star_trivial, hR.isSelfAdjoint.star_eq] at hds
  rw [whitening, mul_smul_comm, hds, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

omit [PartialOrder A] [StarOrderedRing A] in
theorem whitening_left_support (R B : A) (hR : IsStarProjection R)
    (hB : IsSelfAdjoint B) (hBR : B*R=B) {c : ℝ} : R*whitening R B c = whitening R B c := by
  have he : normalizer R B c*R = normalizer R B c := by
    have hs' : star B*R = star B := by simpa only [hB.star_eq] using hBR
    unfold normalizer
    rw [smul_mul_assoc, mul_assoc, hs']
  have he' := congrArg star he
  simp only [star_mul, hR.isSelfAdjoint.star_eq] at he'
  rw [whitening, mul_smul_comm, he']

#print axioms whitening_norm_le
#print axioms whitening_right_inverse
#print axioms whitening_left_support

end QuantitativeSpectralWhitening
