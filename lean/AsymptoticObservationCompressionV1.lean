module

public import AsymptoticObservationOperatorV1

set_option autoImplicit false

@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct

variable {G H J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- Compression of the observation operator to a closed holomorphic
subspace, regarded as an operator on the ambient Hilbert space. -/
noncomputable def compression (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (U : Submodule ℂ H) [U.HasOrthogonalProjection] : H →L[ℂ] H :=
  U.starProjection.comp ((operator R L hR).comp U.starProjection)

theorem compression_positive (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    (compression R L hR U).IsPositive :=
  (operator_positive R L hR).conj_starProjection U

theorem compression_norm_apply_le (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (U : Submodule ℂ H) [U.HasOrthogonalProjection] (x : H) :
    ‖compression R L hR U x‖≤‖x‖ :=
  (U.norm_starProjection_apply_le _).trans
    ((operator_norm_apply_le R L hR _).trans (U.norm_starProjection_apply_le x))

theorem compression_norm_le_one (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    ‖compression R L hR U‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [one_mul] using compression_norm_apply_le R L hR U x

/-- Reconstructed holomorphic solutions belong to the one-eigenspace. -/
theorem compression_fixes (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    {g : G} (hg : L (R g)=0) (hU : R g∈U) : compression R L hR U (R g)=R g := by
  simp only [compression,comp_apply,U.starProjection_eq_self_iff.mpr hU,operator_fixes R L hR hg]

theorem compression_inner (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (U : Submodule ℂ H) [U.HasOrthogonalProjection] (x : H) :
    ⟪compression R L hR U x,x⟫_ℂ =
      ⟪operator R L hR (U.starProjection x),U.starProjection x⟫_ℂ := by
  exact U.inner_starProjection_left_eq_right _ _

/-- The compressed common majorant, for use on the normalized Fourier basis. -/
theorem compression_re_inner_le_gram (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (U : Submodule ℂ H) [U.HasOrthogonalProjection] (x : H) :
    (⟪compression R L hR U x,x⟫_ℂ).re≤‖R.adjoint (U.starProjection x)‖^2 := by
  rw [compression_inner]
  exact operator_re_inner_le_gram R L hR _

#print axioms compression_positive
#print axioms compression_norm_le_one
#print axioms compression_fixes
#print axioms compression_re_inner_le_gram

end AsymptoticObservation
