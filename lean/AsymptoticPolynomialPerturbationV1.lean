module

public import AsymptoticInversePolynomialV1
public import AsymptoticFiniteNeumannPerturbationV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticReconstruction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A power is uniformly Lipschitz on each bounded set of operators.
The estimate does not require commutativity or a contraction. -/
theorem power_difference_norm_le_of_bound (M N : H →L[ℂ] H) {D : ℝ}
    (hD : 1≤D) (hM : ‖M‖≤D) (hN : ‖N‖≤D) (n : ℕ) :
    ‖M^n-N^n‖≤(n:ℝ)*D^n*‖M-N‖ := by
  have hD0 : 0≤D := zero_le_one.trans hD
  induction n with
  | zero => simp
  | succ n ih =>
    have he : M^(n+1)-N^(n+1)=M*(M^n-N^n)+(M-N)*N^n := by
      rw [pow_succ',pow_succ']
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖M‖*‖M^n-N^n‖+‖M-N‖*‖N^n‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ D*((n:ℝ)*D^n*‖M-N‖)+‖M-N‖*D^n :=
        add_le_add (mul_le_mul hM ih (norm_nonneg _) hD0)
          (mul_le_mul_of_nonneg_left (power_norm_le N hN n) (norm_nonneg _))
      _ ≤ D*((n:ℝ)*D^n*‖M-N‖)+D*(‖M-N‖*D^n) := by
        have hx : 0≤‖M-N‖*D^n := mul_nonneg (norm_nonneg _) (pow_nonneg hD0 n)
        have hh := mul_le_mul_of_nonneg_right hD hx
        simpa only [one_mul] using add_le_add le_rfl hh
      _ = _ := by rw [pow_succ]; push_cast; ring

#print axioms power_difference_norm_le_of_bound

end AsymptoticReconstruction

namespace AsymptoticCoerciveNeumann

open ContinuousLinearMap Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable def polynomialBound (C D : ℝ) (n : ℕ) : ℝ :=
  scale C*∑ j∈Finset.range n,(1+scale C*D)^j

noncomputable def polynomialLipschitz (C D : ℝ) (n : ℕ) : ℝ :=
  (scale C)^2*∑ j∈Finset.range n,(j:ℝ)*(1+scale C*D)^j

theorem step_norm_le_of_bound (C : ℝ) (M : H →L[ℂ] H) {D : ℝ} (hM : ‖M‖≤D) :
    ‖step C M‖≤1+scale C*D := by
  apply (norm_sub_le _ _).trans
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (scale_pos C)]
  exact add_le_add norm_id_le (mul_le_mul_of_nonneg_left hM (scale_pos C).le)

theorem step_difference_norm (C : ℝ) (M N : H →L[ℂ] H) :
    ‖step C M-step C N‖=scale C*‖M-N‖ := by
  have he : step C M-step C N=(scale C:ℂ) • (N-M) := by
    simp only [step,smul_sub]
    abel
  rw [he,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (scale_pos C),norm_sub_rev]

theorem polynomial_norm_le_of_bound (C : ℝ) (M : H →L[ℂ] H) {D : ℝ} (hM : ‖M‖≤D) (n : ℕ) :
    ‖polynomial C M n‖≤polynomialBound C D n := by
  rw [polynomial,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (scale_pos C)]
  apply mul_le_mul_of_nonneg_left _ (scale_pos C).le
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ =>
    AsymptoticReconstruction.power_norm_le (step C M) (step_norm_le_of_bound C M hM) j))

/-- A fixed polynomial remains uniformly stable when a finite branch
approximation is substituted into its normal operator. The approximate
operator need not itself be invertible or positive. -/
theorem polynomial_difference_norm_le (C : ℝ) (M N : H →L[ℂ] H) {D : ℝ}
    (hM : ‖M‖≤D) (hN : ‖N‖≤D) (n : ℕ) :
    ‖polynomial C M n-polynomial C N n‖≤polynomialLipschitz C D n*‖M-N‖ := by
  have hD : 0≤D := (norm_nonneg M).trans hM
  have hs : 1≤1+scale C*D := by nlinarith [scale_pos C]
  rw [polynomial,polynomial,← smul_sub,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (scale_pos C),← Finset.sum_sub_distrib]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (scale_pos C).le).trans
  have hp := Finset.sum_le_sum (s:=Finset.range n) (fun j _ =>
    AsymptoticReconstruction.power_difference_norm_le_of_bound (step C M) (step C N) hs
      (step_norm_le_of_bound C M hM) (step_norm_le_of_bound C N hN) j)
  apply (mul_le_mul_of_nonneg_left hp (scale_pos C).le).trans_eq
  rw [step_difference_norm]
  simp only [polynomialLipschitz,← Finset.sum_mul]
  ring

theorem polynomial_tendstoUniformly_of_approximations {α ι : Type*} {l : Filter ι}
    (C D : ℝ) (hD : 0≤D) (M : α → H →L[ℂ] H) (F : ι → α → H →L[ℂ] H)
    (hM : ∀ a,‖M a‖≤D) (hF : ∀ i a,‖F i a‖≤D) (hf : TendstoUniformly F M l) (n : ℕ) :
    TendstoUniformly (fun i a => polynomial C (F i a) n) (fun a => polynomial C (M a) n) l := by
  have hscale : 0<scale C := scale_pos C
  have hL : 0≤polynomialLipschitz C D n := by
    unfold polynomialLipschitz
    positivity
  have hL1 : 0<1+polynomialLipschitz C D n := by linarith
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hδ : 0<ε/(1+polynomialLipschitz C D n) := div_pos hε hL1
  apply ((Metric.tendstoUniformly_iff.mp hf) _ hδ).mono
  intro i hi a
  have hd : ‖F i a-M a‖<ε/(1+polynomialLipschitz C D n) := by
    simpa only [dist_eq_norm,norm_sub_rev] using hi a
  rw [dist_eq_norm,norm_sub_rev]
  apply (polynomial_difference_norm_le C (F i a) (M a) (hF i a) (hM a) n).trans_lt
  have hb := mul_le_mul_of_nonneg_left hd.le hL
  have he : (1+polynomialLipschitz C D n)*(ε/(1+polynomialLipschitz C D n))=ε :=
    mul_div_cancel₀ ε hL1.ne'
  nlinarith

#print axioms step_norm_le_of_bound
#print axioms step_difference_norm
#print axioms polynomial_norm_le_of_bound
#print axioms polynomial_difference_norm_le
#print axioms polynomial_tendstoUniformly_of_approximations

end AsymptoticCoerciveNeumann
