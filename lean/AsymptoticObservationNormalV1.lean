module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct ComplexConjugate

variable {G H J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- The normal operator R*R + (LR)*(LR), for bounded reconstruction R and
one fixed stack L of observation residuals. -/
noncomputable def normal (R : G →L[ℂ] H) (L : H →L[ℂ] J) : G →L[ℂ] G :=
  R.adjoint.comp R + (L.comp R).adjoint.comp (L.comp R)

/-- The normal quadratic form is the sum of two nonnegative energies. -/
theorem normal_inner (R : G →L[ℂ] H) (L : H →L[ℂ] J) (g : G) :
    ⟪normal R L g,g⟫_ℂ = (‖R g‖^2:ℝ)+(‖L (R g)‖^2:ℝ) := by
  simp only [normal,add_apply,comp_apply,inner_add_left,adjoint_inner_left,
    inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
  rfl

theorem normal_re_inner (R : G →L[ℂ] H) (L : H →L[ℂ] J) (g : G) :
    (⟪normal R L g,g⟫_ℂ).re = ‖R g‖^2+‖L (R g)‖^2 := by
  rw [normal_inner]
  simp only [Complex.add_re,Complex.ofReal_re]

/-- The terminal identity implies norm domination. Under that domination,
the normal operator has lower bound one. -/
theorem normal_coercive (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (g : G) : ‖g‖^2≤(⟪normal R L g,g⟫_ℂ).re := by
  rw [normal_re_inner]
  nlinarith [hR g,norm_nonneg g,norm_nonneg (R g),sq_nonneg ‖L (R g)‖]

theorem normal_bounded_below (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (g : G) : ‖g‖≤‖normal R L g‖ := by
  by_cases hg : g=0
  · simp [hg]
  have hgpos : 0<‖g‖ := norm_pos_iff.mpr hg
  have henergy := normal_coercive R L hR g
  have hcs := re_inner_le_norm (𝕜:=ℂ) (normal R L g) g
  change (⟪normal R L g,g⟫_ℂ).re≤‖normal R L g‖*‖g‖ at hcs
  nlinarith

theorem normal_antilipschitz (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) : AntilipschitzWith 1 (normal R L) := by
  apply (normal R L).antilipschitz_of_bound
  simpa only [NNReal.coe_one,one_mul] using normal_bounded_below R L hR

theorem normal_range_closed (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) : IsClosed ((normal R L).range : Set G) :=
  (normal_antilipschitz R L hR).isClosed_range (normal R L).uniformContinuous

/-- Surjectivity follows from closed range and the trivial orthogonal
complement, without a finite-dimensional or spectral assumption. -/
theorem normal_range_top (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) : (normal R L).range=⊤ := by
  let : CompleteSpace (normal R L).range := (normal_range_closed R L hR).completeSpace_coe
  rw [← (normal R L).range.orthogonal_orthogonal,Submodule.eq_top_iff']
  intro v w hw
  have he : ⟪normal R L w,w⟫_ℂ=0 := hw _ ⟨w,rfl⟩
  have henergy := normal_coercive R L hR w
  rw [he] at henergy
  have hw0 : w=0 := by
    apply norm_eq_zero.mp
    change ‖w‖^2≤0 at henergy
    nlinarith [norm_nonneg w]
  simp [hw0]

/-- The actual bounded inverse used by the observation construction. -/
noncomputable def normalEquiv (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) : G ≃L[ℂ] G :=
  ContinuousLinearEquiv.ofBijective (normal R L)
    (LinearMap.ker_eq_bot.mpr (normal_antilipschitz R L hR).injective)
    (normal_range_top R L hR)

@[simp] theorem normalEquiv_apply (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (g : G) : normalEquiv R L hR g=normal R L g := rfl

theorem inverse_norm_le (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (g : G) : ‖(normalEquiv R L hR).symm g‖≤‖g‖ := by
  have hh := normal_bounded_below R L hR ((normalEquiv R L hR).symm g)
  simpa only [← normalEquiv_apply R L hR,ContinuousLinearEquiv.apply_symm_apply] using hh

#print axioms normal_range_top
#print axioms normalEquiv
#print axioms inverse_norm_le

end AsymptoticObservation
