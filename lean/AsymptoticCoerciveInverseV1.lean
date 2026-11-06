module

public import AsymptoticCoerciveNeumannV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCoerciveNeumann

open ContinuousLinearMap InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem one_sub_step (C : ℝ) (M : H →L[ℂ] H) : 1-step C M=(scale C:ℂ) • M :=
  sub_sub_cancel _ _

theorem inverse_mul (C : ℝ) (M : H →L[ℂ] H) (hM : ‖M‖≤C)
    (hc : ∀ x,‖x‖^2≤(⟪M x,x⟫_ℂ).re) : (inverse C M).comp M=1 := by
  have hs := geom_series_mul_neg (step C M) (step_norm_lt_one C M hM hc)
  rw [one_sub_step] at hs
  change ((scale C:ℂ) • ∑' n : ℕ,(step C M)^n)*M=1
  rw [smul_mul_assoc,← mul_smul_comm]
  exact hs

theorem mul_inverse (C : ℝ) (M : H →L[ℂ] H) (hM : ‖M‖≤C)
    (hc : ∀ x,‖x‖^2≤(⟪M x,x⟫_ℂ).re) : M.comp (inverse C M)=1 := by
  have hs := mul_neg_geom_series (step C M) (step_norm_lt_one C M hM hc)
  rw [one_sub_step] at hs
  change M*((scale C:ℂ) • ∑' n : ℕ,(step C M)^n)=1
  rw [mul_smul_comm,← smul_mul_assoc]
  exact hs

theorem inverse_apply_mul (C : ℝ) (M : H →L[ℂ] H) (hM : ‖M‖≤C)
    (hc : ∀ x,‖x‖^2≤(⟪M x,x⟫_ℂ).re) (x : H) : inverse C M (M x)=x :=
  congrArg (fun T : H →L[ℂ] H => T x) (inverse_mul C M hM hc)

theorem mul_apply_inverse (C : ℝ) (M : H →L[ℂ] H) (hM : ‖M‖≤C)
    (hc : ∀ x,‖x‖^2≤(⟪M x,x⟫_ℂ).re) (x : H) : M (inverse C M x)=x :=
  congrArg (fun T : H →L[ℂ] H => T x) (mul_inverse C M hM hc)

omit [CompleteSpace H] in
theorem bounded_below (M : H →L[ℂ] H)
    (hc : ∀ x,‖x‖^2≤(⟪M x,x⟫_ℂ).re) (x : H) : ‖x‖≤‖M x‖ := by
  have hcs := re_inner_le_norm (𝕜:=ℂ) (M x) x
  change (⟪M x,x⟫_ℂ).re≤‖M x‖*‖x‖ at hcs
  have hcx := hc x
  nlinarith [norm_nonneg x,norm_nonneg (M x)]

theorem inverse_norm_le (C : ℝ) (M : H →L[ℂ] H) (hM : ‖M‖≤C)
    (hc : ∀ x,‖x‖^2≤(⟪M x,x⟫_ℂ).re) : ‖inverse C M‖≤1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  simpa only [mul_apply_inverse C M hM hc x,one_mul] using bounded_below M hc (inverse C M x)

#print axioms inverse_mul
#print axioms mul_inverse
#print axioms inverse_norm_le

end AsymptoticCoerciveNeumann
