module

public import QuantitativeSpectralCutPolarV1
public import AsymptoticPolarBoundsV1
public import QuantitativeSpectralCutRowV1
public import QuantitativeSpectralWhiteningV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralCutWhitening

open ContinuousLinearMap InnerProductSpace AsymptoticPolarIsometry
open QuantitativeSpectralCutPolar QuantitativeSpectralCutRow QuantitativeSpectralWhitening

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]


theorem absolute_cut_source (X : H →L[ℂ] J) {c : ℝ} (hc : 0 < c) :
    absolute (cutOperator X c) * (cutSpace X c).starProjection = absolute (cutOperator X c) := by
  ext v
  have hv := (cutSpace X c).sub_starProjection_mem_orthogonal v
  rw [← cutOperator_kernel X hc, ← absolute_ker] at hv
  change absolute (cutOperator X c) (v - (cutSpace X c).starProjection v) = 0 at hv
  rw [map_sub, sub_eq_zero] at hv
  exact hv.symm

theorem absolute_cut_coercive (X : H →L[ℂ] J) (c : ℝ) :
    c^2 • (cutSpace X c).starProjection ≤ (cutSpace X c).starProjection * star (absolute (cutOperator X c)) *
      absolute (cutOperator X c) * (cutSpace X c).starProjection := by
  have hr : IsStarProjection ((cutSpace X c).starProjection) :=
    ⟨Submodule.isIdempotentElem_starProjection _,
      isSelfAdjoint_iff'.mpr (isSelfAdjoint_starProjection _)⟩
  have hid : removed (absolute X) c = (cutSpace X c).starProjection := by
    unfold removed cutSpace
    congr 2
    exact absolute_gram X
  have hh := removed_coercive (absolute X) c
  rw [hid] at hh
  have he : star (absolute (cutOperator X c)) * absolute (cutOperator X c) =
      (cutSpace X c).starProjection * (star (absolute X) * absolute X) * (cutSpace X c).starProjection := by
    change (absolute (cutOperator X c)).adjoint.comp (absolute (cutOperator X c)) = _
    rw [absolute_gram]
    change (X.comp ((cutSpace X c).starProjection)).adjoint.comp (X.comp ((cutSpace X c).starProjection)) = _
    rw [adjoint_comp, show (cutSpace X c).starProjection.adjoint = (cutSpace X c).starProjection from isSelfAdjoint_starProjection _]
    rw [show star (absolute X) * absolute X = X.adjoint.comp X from absolute_gram X]
    rfl
  rw [mul_assoc ((cutSpace X c).starProjection) (star (absolute (cutOperator X c))), he]
  simpa only [mul_assoc, hr.isIdempotentElem.eq, ← mul_assoc (cutSpace X c).starProjection (cutSpace X c).starProjection] using hh

/-- Explicit bounded whitening for a genuine rectangular high spectral cut. -/
def cutWhitening (X : H →L[ℂ] J) (c : ℝ) : H →L[ℂ] H :=
  whitening ((cutSpace X c).starProjection) (absolute (cutOperator X c)) c

theorem cutWhitening_norm (X : H →L[ℂ] J) {c : ℝ} (hc : 0 < c) :
    ‖cutWhitening X c‖ ≤ c⁻¹ :=
  whitening_norm_le _ _ ⟨Submodule.isIdempotentElem_starProjection _,
    isSelfAdjoint_iff'.mpr (isSelfAdjoint_starProjection _)⟩ hc (absolute_cut_coercive X c)

theorem cutWhitening_source (X : H →L[ℂ] J) {c : ℝ} (hc : 0 < c) :
    (cutSpace X c).starProjection * cutWhitening X c = cutWhitening X c :=
  whitening_left_support _ _ ⟨Submodule.isIdempotentElem_starProjection _,
    isSelfAdjoint_iff'.mpr (isSelfAdjoint_starProjection _)⟩
    (absolute_nonneg (cutOperator X c)).isSelfAdjoint (absolute_cut_source X hc)

theorem cutWhitening_factor (X : H →L[ℂ] J) {c : ℝ} (hc : 0 < c) :
    X.comp (cutWhitening X c) = polar (cutOperator X c) := by
  have hi := whitening_right_inverse ((cutSpace X c).starProjection) (absolute (cutOperator X c))
    ⟨Submodule.isIdempotentElem_starProjection _,
      isSelfAdjoint_iff'.mpr (isSelfAdjoint_starProjection _)⟩
    (absolute_nonneg (cutOperator X c)).isSelfAdjoint (absolute_cut_source X hc)
    hc (absolute_cut_coercive X c)
  calc
    X.comp (cutWhitening X c) = (cutOperator X c).comp (cutWhitening X c) := by
      change X.comp _ = (X.comp ((cutSpace X c).starProjection)).comp _
      rw [comp_assoc, show ((cutSpace X c).starProjection).comp (cutWhitening X c) = cutWhitening X c from
        cutWhitening_source X hc]
    _ = (polar (cutOperator X c)).comp
        ((absolute (cutOperator X c)).comp (cutWhitening X c)) := by
      rw [← comp_assoc, polar_factor]
    _ = polar (cutOperator X c) := by
      rw [show (absolute (cutOperator X c)).comp (cutWhitening X c) = (cutSpace X c).starProjection from hi,
        polar_cut_source X hc]

#print axioms absolute_cut_source
#print axioms absolute_cut_coercive
#print axioms cutWhitening_norm
#print axioms cutWhitening_source
#print axioms cutWhitening_factor

end QuantitativeSpectralCutWhitening
