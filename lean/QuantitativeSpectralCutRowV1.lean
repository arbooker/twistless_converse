module

public import QuantitativeSpectralCutV1
public import QuantitativeSpectralNormalizedRowV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralCutRow

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The removed projection of the actual continuous-functional-calculus cut. -/
def removed (B : H →L[ℂ] H) (c : ℝ) : H →L[ℂ] H :=
  (QuantitativeSpectralCut.highAt (star B * B) (c^2)).starProjection

/-- The complementary retained projection; it contains threshold eigenvectors. -/
def retained (B : H →L[ℂ] H) (c : ℝ) : H →L[ℂ] H :=
  (QuantitativeSpectralCut.lowAt (star B * B) (c^2)).starProjection

theorem removed_projection (B : H →L[ℂ] H) (c : ℝ) : IsStarProjection (removed B c) := by
  exact ⟨Submodule.isIdempotentElem_starProjection _,
    isSelfAdjoint_iff'.mpr (isSelfAdjoint_starProjection _)⟩

/-- Coercivity is proved for the actual spectral cut, rather than supplied as
an input to the inverse-row construction. -/
theorem removed_coercive (B : H →L[ℂ] H) (c : ℝ) :
    c^2 • removed B c ≤ removed B c * star B * B * removed B c := by
  let R := removed B c
  have hR : IsStarProjection R := removed_projection B c
  have hs : IsSelfAdjoint (R * star B * B * R - c^2 • R) := by
    apply IsSelfAdjoint.sub
    · change star (R * star B * B * R) = _
      simp only [star_mul, star_star, hR.isSelfAdjoint.star_eq, mul_assoc]
    · exact (IsSelfAdjoint.all (c^2)).smul hR.isSelfAdjoint
  apply (le_def).mpr
  apply (isPositive_iff_complex _).mpr
  intro x
  refine ⟨LinearMap.IsSymmetric.coe_re_inner_apply_self (isSelfAdjoint_iff_isSymmetric.mp hs) x, ?_⟩
  have hh := QuantitativeSpectralCut.quadratic_ge_on_highAt (star B * B)
    (IsSelfAdjoint.star_mul_self B) (c^2)
    ((QuantitativeSpectralCut.highAt (star B * B) (c^2)).starProjection_apply_mem x)
  have he : ⟪(R * star B * B * R) x, x⟫_ℂ = ⟪(star B * B) (R x), R x⟫_ℂ := by
    change ⟪R (B.adjoint (B (R x))), x⟫_ℂ = _
    exact (isSelfAdjoint_iff_isSymmetric.mp hR.isSelfAdjoint) _ _
  change 0 ≤ (⟪(R * star B * B * R - c^2 • R) x, x⟫_ℂ).re
  rw [sub_apply, inner_sub_left, Complex.sub_re, he, smul_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left]
  have hp : (⟪R x, x⟫_ℂ).re = ‖R x‖^2 := by
    simpa only [R, removed, Submodule.starProjection_apply, Submodule.norm_coe, RCLike.re_eq_complex_re] using
      (Submodule.re_inner_starProjection_eq_normSq (𝕜 := ℂ)
        (QuantitativeSpectralCut.highAt (star B * B) (c^2)) x)
  simp only [Complex.smul_re, smul_eq_mul, hp]
  exact sub_nonneg.mpr hh

/-- Opposite cuts have an exactly zero compressed Gram block. -/
theorem removed_gram_retained (B : H →L[ℂ] H) (c : ℝ) :
    removed B c * star B * B * retained B c = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change ⟪y, (removed B c) (B.adjoint (B (retained B c x)))⟫_ℂ = ⟪y, 0⟫_ℂ
  have he : ⟪y, (removed B c) (B.adjoint (B (retained B c x)))⟫_ℂ =
      ⟪removed B c y, B.adjoint (B (retained B c x))⟫_ℂ :=
    ((isSelfAdjoint_iff_isSymmetric.mp (removed_projection B c).isSelfAdjoint) y _).symm
  rw [he, adjoint_inner_right, inner_zero_right]
  exact QuantitativeSpectralCut.residual_images_orthogonal B (c^2)
    ((QuantitativeSpectralCut.highAt (star B * B) (c^2)).starProjection_apply_mem y)
    ((QuantitativeSpectralCut.lowAt (star B * B) (c^2)).starProjection_apply_mem x)

/-- The explicit inverse normalizer for an actual high spectral cut. -/
def cutNormalizer (B : H →L[ℂ] H) (c : ℝ) : H →L[ℂ] H :=
  QuantitativeSpectralNormalizedRow.normalizer (removed B c) B c

theorem cutNormalizer_contracts (B : H →L[ℂ] H) {c : ℝ} (hc : 0 < c) :
    ‖cutNormalizer B c‖ ≤ 1 :=
  QuantitativeSpectralNormalizedRow.normalizer_norm_le_one _ _ (removed_projection B c) _
    hc (removed_coercive B c)

theorem cutNormalizer_diagonal (B : H →L[ℂ] H) {c : ℝ} (hc : 0 < c) :
    cutNormalizer B c * B * removed B c = c • removed B c :=
  QuantitativeSpectralNormalizedRow.normalized_diagonal _ _ (removed_projection B c) _
    hc (removed_coercive B c)

theorem cutNormalizer_retained (B : H →L[ℂ] H) (c : ℝ) :
    cutNormalizer B c * B * retained B c = 0 :=
  QuantitativeSpectralNormalizedRow.normalized_off_diagonal _ _ _ _ (removed_gram_retained B c)

#print axioms removed_coercive
#print axioms removed_gram_retained
#print axioms cutNormalizer_contracts
#print axioms cutNormalizer_diagonal
#print axioms cutNormalizer_retained

end QuantitativeSpectralCutRow
