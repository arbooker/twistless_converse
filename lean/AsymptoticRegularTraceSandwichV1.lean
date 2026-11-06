module

public import AsymptoticRegularTraceCyclicV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap
open scoped lp ENNReal

variable {G α : Type*} [Group G] [MeasurableSpace α]

theorem signedTrace_adjoint (μ : Measure α) (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) :
    signedTrace μ (fun x => (B x).adjoint)=signedTrace μ B := by
  simp only [signedTrace,matrix_adjoint,Complex.conj_re]

theorem trace_gram_comp_le (μ : Measure α) (I B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hi : ∀ x,‖I x‖≤1) :
    trace μ (fun x => ((I x).comp (B x)).adjoint.comp ((I x).comp (B x)))≤
      trace μ (fun x => (B x).adjoint.comp (B x)) := by
  rw [trace_gram,trace_gram]
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  have hn : ‖I x (B x (delta 1))‖≤‖B x (delta 1)‖ := by
    simpa only [one_mul] using (I x).le_of_opNorm_le (hi x) (B x (delta 1))
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

variable [Countable G] [MulAction G α]

/-- Transfer the signed trace of a sandwich to its source without
introducing an inverse square root. This follows from square-integrable
polarization and the equality of the real traces of an operator and its
adjoint. -/
theorem signedTrace_sandwich (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (F I : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hF : ∀ g h,Measurable (fun x => matrix (F x) g h))
    (hI : ∀ g h,Measurable (fun x => matrix (I x) g h))
    (hcF : Covariant F) (hcI : Covariant I)
    (hf : trace μ (fun x => (F x).adjoint.comp (F x))<∞) (hi : ∀ x,‖I x‖≤1) :
    signedTrace μ (fun x => (F x).comp ((I x).comp (F x).adjoint))=
      signedTrace μ (fun x => (I x).comp ((F x).adjoint.comp (F x))) := by
  have hFa := matrix_adjoint_measurable F hF
  have hIFa := matrix_comp_measurable I (fun x => (F x).adjoint) hI hFa
  have hf' : trace μ (fun x => ((F x).adjoint).adjoint.comp (F x).adjoint)<∞ := by
    simp only [adjoint_adjoint]
    rw [← trace_adjoint_mul hmp F hF hcF]
    exact hf
  have hif := (trace_gram_comp_le μ I (fun x => (F x).adjoint) hi).trans_lt hf'
  have he := signedTrace_adjoint_mul μ hmp (fun x => (F x).adjoint)
    (fun x => (I x).comp (F x).adjoint) hFa hIFa
    (covariant_adjoint F hcF) (covariant_comp _ _ hcI (covariant_adjoint F hcF)) hf' hif
  simp only [adjoint_adjoint,adjoint_comp] at he
  have ha := signedTrace_adjoint μ (fun x => (F x).adjoint.comp ((F x).comp (I x).adjoint))
  simp only [adjoint_adjoint,adjoint_comp] at ha
  exact he.trans ha.symm

#print axioms trace_gram_comp_le
#print axioms signedTrace_sandwich

end AsymptoticRegularTrace
