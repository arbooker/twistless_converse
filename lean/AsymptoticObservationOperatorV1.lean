module

public import AsymptoticObservationNormalV1

set_option autoImplicit false

@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct

variable {G H J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- The positive observation operator R (R*(1+L*L) R)⁻¹ R*.
Its inverse is constructed from the reconstruction lower bound. -/
noncomputable def operator (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) : H →L[ℂ] H :=
  R.comp ((normalEquiv R L hR).symm.toContinuousLinearMap.comp R.adjoint)

@[simp] theorem operator_apply (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (x : H) :
    operator R L hR x = R ((normalEquiv R L hR).symm (R.adjoint x)) := rfl

theorem normal_formula (R : G →L[ℂ] H) (L : H →L[ℂ] J) :
    normal R L=R.adjoint.comp ((1+L.adjoint.comp L).comp R) := by
  ext g
  simp [normal,adjoint_comp]

/-- The quadratic form identity gives positivity and contraction directly,
without introducing an inverse square root. -/
theorem operator_inner (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (x : H) :
    ⟪operator R L hR x,x⟫_ℂ =
      (‖operator R L hR x‖^2:ℝ)+(‖L (operator R L hR x)‖^2:ℝ) := by
  let g := (normalEquiv R L hR).symm (R.adjoint x)
  have hg : normal R L g=R.adjoint x := (normalEquiv R L hR).apply_symm_apply _
  change ⟪R g,x⟫_ℂ=(‖R g‖^2:ℝ)+(‖L (R g)‖^2:ℝ)
  rw [← adjoint_inner_right,← hg,← inner_conj_symm,normal_inner]
  simp only [map_add,Complex.conj_ofReal]

theorem operator_re_inner (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (x : H) :
    (⟪operator R L hR x,x⟫_ℂ).re =
      ‖operator R L hR x‖^2+‖L (operator R L hR x)‖^2 := by
  rw [operator_inner]
  simp only [Complex.add_re,Complex.ofReal_re]

theorem operator_positive (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) : (operator R L hR).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  change ((⟪operator R L hR x,x⟫_ℂ).re:ℂ)=⟪operator R L hR x,x⟫_ℂ ∧
    0≤(⟪operator R L hR x,x⟫_ℂ).re
  rw [operator_inner]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.ofReal_add]
  exact ⟨trivial,add_nonneg (sq_nonneg _) (sq_nonneg _)⟩

theorem operator_norm_apply_le (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (x : H) : ‖operator R L hR x‖≤‖x‖ := by
  have he := operator_re_inner R L hR x
  have hcs := re_inner_le_norm (𝕜:=ℂ) (operator R L hR x) x
  change (⟪operator R L hR x,x⟫_ℂ).re≤‖operator R L hR x‖*‖x‖ at hcs
  nlinarith [sq_nonneg ‖L (operator R L hR x)‖,norm_nonneg (operator R L hR x),norm_nonneg x]

theorem operator_norm_le_one (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) : ‖operator R L hR‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [one_mul] using operator_norm_apply_le R L hR x

/-- Every reconstructed vector satisfying the known observations is fixed. -/
theorem operator_fixes (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) {g : G} (hg : L (R g)=0) :
    operator R L hR (R g)=R g := by
  have he : normal R L g=R.adjoint (R g) := by
    simp [normal,hg]
  rw [operator_apply,← he,← normalEquiv_apply R L hR,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The common majorant A ≤ R R*, in quadratic-form form. -/
theorem operator_re_inner_le_gram (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (x : H) :
    (⟪operator R L hR x,x⟫_ℂ).re≤‖R.adjoint x‖^2 := by
  rw [operator_apply,← adjoint_inner_right]
  have hcs := re_inner_le_norm (𝕜:=ℂ) ((normalEquiv R L hR).symm (R.adjoint x)) (R.adjoint x)
  change (⟪(normalEquiv R L hR).symm (R.adjoint x),R.adjoint x⟫_ℂ).re≤
    ‖(normalEquiv R L hR).symm (R.adjoint x)‖*‖R.adjoint x‖ at hcs
  have hn := inverse_norm_le R L hR (R.adjoint x)
  nlinarith [norm_nonneg (R.adjoint x)]

#print axioms operator_positive
#print axioms operator_norm_le_one
#print axioms operator_fixes
#print axioms operator_re_inner_le_gram

end AsymptoticObservation
