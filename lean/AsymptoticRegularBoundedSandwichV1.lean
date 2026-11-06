module

public import AsymptoticRegularTraceSandwichV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap
open scoped lp ENNReal

variable {G α : Type*} [Group G] [MeasurableSpace α]

theorem trace_gram_comp_le_of_bound (μ : Measure α)
    (I B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) {C : ℝ}
    (hi : ∀ x,‖I x‖≤C) :
    trace μ (fun x => ((I x).comp (B x)).adjoint.comp ((I x).comp (B x)))≤
      ENNReal.ofReal (C^2)*trace μ (fun x => (B x).adjoint.comp (B x)) := by
  rw [trace_gram,trace_gram,← lintegral_const_mul' _ _]
  apply lintegral_mono
  intro x
  dsimp only
  rw [← ENNReal.ofReal_mul (sq_nonneg C)]
  apply ENNReal.ofReal_le_ofReal
  have hn := (I x).le_of_opNorm_le (hi x) (B x (delta 1))
  simpa only [comp_apply,mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  all_goals finiteness

theorem trace_gram_comp_finite_of_bound (μ : Measure α)
    (I B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) {C : ℝ}
    (hi : ∀ x,‖I x‖≤C) (hf : trace μ (fun x => (B x).adjoint.comp (B x))<∞) :
    trace μ (fun x => ((I x).comp (B x)).adjoint.comp ((I x).comp (B x)))<∞ :=
  (trace_gram_comp_le_of_bound μ I B hi).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)

variable [Countable G] [MulAction G α]

/-- Cyclicity for a finite-Gram reconstruction and any uniformly bounded
middle family. In particular the finite inverse polynomials need not be
positive or contractions. -/
theorem signedTrace_bounded_sandwich (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (F I : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hF : ∀ g h,Measurable (fun x => matrix (F x) g h))
    (hI : ∀ g h,Measurable (fun x => matrix (I x) g h))
    (hcF : Covariant F) (hcI : Covariant I)
    (hf : trace μ (fun x => (F x).adjoint.comp (F x))<∞)
    {C : ℝ} (hi : ∀ x,‖I x‖≤C) :
    signedTrace μ (fun x => (F x).comp ((I x).comp (F x).adjoint))=
      signedTrace μ (fun x => (I x).comp ((F x).adjoint.comp (F x))) := by
  have hFa := matrix_adjoint_measurable F hF
  have hIFa := matrix_comp_measurable I (fun x => (F x).adjoint) hI hFa
  have hf' : trace μ (fun x => ((F x).adjoint).adjoint.comp (F x).adjoint)<∞ := by
    simp only [adjoint_adjoint]
    rw [← trace_adjoint_mul hmp F hF hcF]
    exact hf
  have hif : trace μ (fun x => ((I x).comp (F x).adjoint).adjoint.comp
      ((I x).comp (F x).adjoint))<∞ :=
    (trace_gram_comp_le_of_bound μ I (fun x => (F x).adjoint) hi).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf')
  have he := signedTrace_adjoint_mul μ hmp (fun x => (F x).adjoint)
    (fun x => (I x).comp (F x).adjoint) hFa hIFa
    (covariant_adjoint F hcF) (covariant_comp _ _ hcI (covariant_adjoint F hcF)) hf' hif
  simp only [adjoint_adjoint,adjoint_comp] at he
  have ha := signedTrace_adjoint μ (fun x => (F x).adjoint.comp ((F x).comp (I x).adjoint))
  simp only [adjoint_adjoint,adjoint_comp] at ha
  exact he.trans ha.symm

theorem bounded_sandwich_diagonal_integrable (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (F I : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hF : ∀ g h,Measurable (fun x => matrix (F x) g h))
    (hI : ∀ g h,Measurable (fun x => matrix (I x) g h))
    (hcF : Covariant F)
    (hf : trace μ (fun x => (F x).adjoint.comp (F x))<∞)
    {C : ℝ} (hi : ∀ x,‖I x‖≤C) :
    Integrable (fun x => (matrix ((F x).comp ((I x).comp (F x).adjoint)) 1 1).re) μ := by
  have hFa := matrix_adjoint_measurable F hF
  have hIFa := matrix_comp_measurable I (fun x => (F x).adjoint) hI hFa
  have hf' : trace μ (fun x => ((F x).adjoint).adjoint.comp (F x).adjoint)<∞ := by
    simp only [adjoint_adjoint]
    rw [← trace_adjoint_mul hmp F hF hcF]
    exact hf
  have hh := cross_integrable μ (fun x => (F x).adjoint)
    (fun x => (I x).comp (F x).adjoint) hFa hIFa
    (energy_integrable μ _ hFa hf')
    (energy_integrable μ _ hIFa (trace_gram_comp_finite_of_bound μ I _ hi hf'))
  simpa only [← matrix_cross,adjoint_adjoint] using hh

#print axioms trace_gram_comp_finite_of_bound
#print axioms bounded_sandwich_diagonal_integrable
#print axioms trace_gram_comp_le_of_bound
#print axioms signedTrace_bounded_sandwich

end AsymptoticRegularTrace
