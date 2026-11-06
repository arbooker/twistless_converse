module

public import AsymptoticNeumannReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCoerciveNeumann

open ContinuousLinearMap InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable def scale (C : ℝ) : ℝ := (C^2+1)⁻¹
noncomputable def rate (C : ℝ) : ℝ := Real.sqrt (1-scale C)

theorem scale_pos (C : ℝ) : 0<scale C := inv_pos.mpr (by positivity)

theorem scale_le_one (C : ℝ) : scale C≤1 := by
  unfold scale
  exact (inv_le_one₀ (by positivity : 0<C^2+1)).mpr (by nlinarith [sq_nonneg C])

theorem scale_identity (C : ℝ) : scale C*(C^2+1)=1 :=
  inv_mul_cancel₀ (by positivity : C^2+1≠0)

theorem rate_sq (C : ℝ) : rate C^2=1-scale C :=
  Real.sq_sqrt (sub_nonneg.mpr (scale_le_one C))

theorem rate_lt_one (C : ℝ) : rate C<1 := by
  have hr := Real.sqrt_nonneg (1-scale C)
  have hs := rate_sq C
  have hc := scale_pos C
  nlinarith

noncomputable def step (C : ℝ) (M : H →L[ℂ] H) : H →L[ℂ] H :=
  1-(scale C:ℂ) • M

theorem step_energy (C : ℝ) (M : H →L[ℂ] H) (x : H) :
    ‖step C M x‖^2=‖x‖^2-2*scale C*(⟪M x,x⟫_ℂ).re+(scale C)^2*‖M x‖^2 := by
  change ‖x-(scale C:ℂ) • M x‖^2=_
  rw [norm_sub_sq (𝕜:=ℂ),inner_smul_right,norm_smul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (scale_pos C)]
  change ‖x‖^2-2*((scale C:ℂ)*⟪x,M x⟫_ℂ).re+(scale C*‖M x‖)^2=_
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hsym : (⟪x,M x⟫_ℂ).re=(⟪M x,x⟫_ℂ).re := inner_re_symm (𝕜:=ℂ) x (M x)
  rw [hsym]
  ring

/-- A uniform contraction follows from a uniform upper norm bound and
coercivity one. Self-adjointness is not needed for this estimate. -/
theorem step_norm_le (C : ℝ) (M : H →L[ℂ] H) (hM : ‖M‖≤C)
    (hc : ∀ x,‖x‖^2≤(⟪M x,x⟫_ℂ).re) : ‖step C M‖≤rate C := by
  apply opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  have hnorm : ‖M x‖^2≤C^2*‖x‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (M x)) (M.le_of_opNorm_le hM x) 2
  have hcx := hc x
  have hscale := scale_pos C
  have hid := scale_identity C
  have he := step_energy C M x
  have h₁ := mul_le_mul_of_nonneg_left hnorm (sq_nonneg (scale C))
  have h₂ := mul_le_mul_of_nonneg_left hcx (by positivity : 0≤2*scale C)
  have hs : ‖step C M x‖^2≤(rate C*‖x‖)^2 := by
    rw [mul_pow,rate_sq]
    have hid' : scale C^2*C^2=scale C-(scale C)^2 := by nlinarith [congrArg (fun y : ℝ => scale C*y) hid]
    have h₃ : scale C^2*(C^2*‖x‖^2)=(scale C-scale C^2)*‖x‖^2 := by rw [← mul_assoc,hid']
    rw [h₃] at h₁
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp hs

theorem step_norm_lt_one (C : ℝ) (M : H →L[ℂ] H) (hM : ‖M‖≤C)
    (hc : ∀ x,‖x‖^2≤(⟪M x,x⟫_ℂ).re) : ‖step C M‖<1 :=
  (step_norm_le C M hM hc).trans_lt (rate_lt_one C)

/-- An explicit norm-convergent series for the inverse, using a common
scale for the entire operator family. -/
noncomputable def inverse (C : ℝ) (M : H →L[ℂ] H) : H →L[ℂ] H :=
  (scale C:ℂ) • ∑' n : ℕ,(step C M)^n

#print axioms step_norm_le
#print axioms step_norm_lt_one

end AsymptoticCoerciveNeumann
