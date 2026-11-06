module

public import AsymptoticCoerciveInverseV1
public import AsymptoticFiniteNeumannV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCoerciveNeumann

open ContinuousLinearMap InnerProductSpace Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The constructed inverse is independent of the numerical bound used
to scale its series. This also identifies it with any given left inverse. -/
theorem inverse_eq_of_left_inverse (C : ℝ) (M : H →L[ℂ] H) (hM : ‖M‖≤C)
    (hc : ∀ x,‖x‖^2≤(⟪M x,x⟫_ℂ).re) (I : H →L[ℂ] H) (hI : I.comp M=1) :
    inverse C M=I := by
  apply ContinuousLinearMap.ext
  intro x
  have hi := congrArg (fun T : H →L[ℂ] H => T (inverse C M x)) hI
  change I (M (inverse C M x))=inverse C M x at hi
  rw [mul_apply_inverse C M hM hc x] at hi
  exact hi.symm

/-- A finite polynomial in the normal operator, with coefficients using
only the common upper bound C. -/
noncomputable def polynomial (C : ℝ) (M : H →L[ℂ] H) (n : ℕ) : H →L[ℂ] H :=
  (scale C:ℂ) • ∑ j∈Finset.range n,(step C M)^j

noncomputable def polynomialError (C : ℝ) (n : ℕ) : ℝ :=
  scale C*(rate C)^n/(1-rate C)

theorem polynomial_error (C : ℝ) (M : H →L[ℂ] H) (hM : ‖M‖≤C)
    (hc : ∀ x,‖x‖^2≤(⟪M x,x⟫_ℂ).re) (n : ℕ) :
    ‖polynomial C M n-inverse C M‖≤polynomialError C n := by
  have hs := summable_geometric_of_norm_lt_one (step_norm_lt_one C M hM hc)
  have he : ‖(∑ j∈Finset.range n,(step C M)^j)-(∑' j : ℕ,(step C M)^j)‖≤
      (rate C)^n/(1-rate C) := by
    simpa only [one_mul] using norm_sub_le_of_geometric_bound_of_hasSum (C:=1) (rate_lt_one C)
      (fun j => by simpa only [one_mul] using
        AsymptoticReconstruction.power_norm_le (step C M) (step_norm_le C M hM hc) j) hs.hasSum n
  rw [polynomial,inverse,← smul_sub,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (scale_pos C)]
  apply (mul_le_mul_of_nonneg_left he (scale_pos C).le).trans_eq
  unfold polynomialError
  ring

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem polynomialError_tendsto_zero (C : ℝ) :
    Tendsto (polynomialError C) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => scale C*(rate C)^n/(1-rate C)) atTop (𝓝 0)
  have hr0 : 0≤rate C := Real.sqrt_nonneg _
  simpa only [mul_zero,zero_div] using
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 (rate_lt_one C)).const_mul (scale C)).div_const (1-rate C)

/-- The same degree approximates all operators in a uniformly bounded
coercive family. The bound remains independent of the holomorphic weight. -/
theorem polynomial_tendstoUniformly {α : Type*} (C : ℝ) (M : α → H →L[ℂ] H)
    (hM : ∀ a,‖M a‖≤C) (hc : ∀ a x,‖x‖^2≤(⟪M a x,x⟫_ℂ).re) :
    TendstoUniformly (fun n a => polynomial C (M a) n) (fun a => inverse C (M a)) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  apply ((tendsto_order.mp (polynomialError_tendsto_zero C)).2 δ hδ).mono
  intro n hn a
  rw [dist_eq_norm,norm_sub_rev]
  exact (polynomial_error C (M a) (hM a) (hc a) n).trans_lt hn

#print axioms inverse_eq_of_left_inverse
#print axioms polynomial_error
#print axioms polynomialError_tendsto_zero
#print axioms polynomial_tendstoUniformly

end AsymptoticCoerciveNeumann
