module

public import QuantitativeMaassRegularTraceLinearityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped lp ENNReal
namespace AsymptoticRegularTrace
variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

theorem finite_gram_product_integrable (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (A B : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hmA : ∀ g h,Measurable (fun x => matrix (A x) g h))
    (hmB : ∀ g h,Measurable (fun x => matrix (B x) g h)) (hcA : Covariant A)
    (hfA : trace μ (fun x => (A x).adjoint.comp (A x))<∞)
    (hfB : trace μ (fun x => (B x).adjoint.comp (B x))<∞) :
    Integrable (fun x => rootDiagonal (A x*B x)) μ := by
  have hmAa := matrix_adjoint_measurable A hmA
  have hfAa : trace μ (fun x => ((A x).adjoint).adjoint.comp (A x).adjoint)<∞ := by
    simp only [adjoint_adjoint]
    rw [←trace_adjoint_mul hmp A hmA hcA]
    exact hfA
  have hh := cross_integrable μ (fun x => (A x).adjoint) B hmAa hmB
    (energy_integrable μ _ hmAa hfAa) (energy_integrable μ B hmB hfB)
  simpa only [←matrix_cross,adjoint_adjoint,rootDiagonal_apply,mul_def] using hh

/-- Cyclicity of two finite-energy regular factors. -/
theorem signedTrace_finite_gram_mul_comm (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (A B : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hmA : ∀ g h,Measurable (fun x => matrix (A x) g h))
    (hmB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hcA : Covariant A) (hcB : Covariant B)
    (hfA : trace μ (fun x => (A x).adjoint.comp (A x))<∞)
    (hfB : trace μ (fun x => (B x).adjoint.comp (B x))<∞) :
    signedTrace μ (fun x => A x*B x)=signedTrace μ (fun x => B x*A x) := by
  have hmAa := matrix_adjoint_measurable A hmA
  have hfAa : trace μ (fun x => ((A x).adjoint).adjoint.comp (A x).adjoint)<∞ := by
    simp only [adjoint_adjoint]
    rw [←trace_adjoint_mul hmp A hmA hcA]
    exact hfA
  have hh := signedTrace_adjoint_mul μ hmp (fun x => (A x).adjoint) B hmAa hmB
    (covariant_adjoint A hcA) hcB hfAa hfB
  simp only [adjoint_adjoint] at hh
  have ha := signedTrace_adjoint μ (fun x => B x*A x)
  simp only [mul_def,adjoint_comp] at ha
  exact hh.trans ha

#print axioms finite_gram_product_integrable
#print axioms signedTrace_finite_gram_mul_comm
end AsymptoticRegularTrace
