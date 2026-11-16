module

public import QuantitativeMaassRegularSupportedTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped lp ENNReal
namespace AsymptoticRegularTrace
variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- A bounded weight times a finite regular Gram family is controlled by
its positive trace. The ambient trace can be infinite. -/
theorem signedTrace_weighted_gram_bound (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (R B : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hR : ∀ g h,Measurable (fun x => matrix (R x) g h))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hcR : Covariant R) (hcB : Covariant B)
    (hf : trace μ (fun x => (R x).adjoint.comp (R x))<∞)
    {C : ℝ} (hb : ∀ x,‖B x‖≤C) :
    |signedTrace μ (fun x => (B x).comp ((R x).adjoint.comp (R x)))|≤
      C*(trace μ (fun x => (R x).adjoint.comp (R x))).toReal := by
  have hRa := matrix_adjoint_measurable R hR
  have ht := trace_adjoint_mul hmp R hR hcR
  have hfa : trace μ (fun x => ((R x).adjoint).adjoint.comp (R x).adjoint)<∞ := by
    simp only [adjoint_adjoint]
    rw [←ht]
    exact hf
  have hh := signedTrace_adjoint_sandwich_bound μ (fun x => (R x).adjoint) B hRa hfa hb
  simp only [adjoint_adjoint] at hh
  rw [signedTrace_bounded_sandwich μ hmp R B hR hB hcR hcB hf hb,←ht] at hh
  exact hh

/-- Multiplying a finite-Gram family on the right by a bounded covariant
family preserves finite energy, by cyclicity and the left-composition bound. -/
theorem trace_gram_right_comp_finite (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (R B : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hR : ∀ g h,Measurable (fun x => matrix (R x) g h))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hcR : Covariant R) (hcB : Covariant B)
    (hf : trace μ (fun x => (R x).adjoint.comp (R x))<∞)
    {C : ℝ} (hb : ∀ x,‖B x‖≤C) :
    trace μ (fun x => ((R x).comp (B x)).adjoint.comp ((R x).comp (B x)))<∞ := by
  have hRa := matrix_adjoint_measurable R hR
  have hBa := matrix_adjoint_measurable B hB
  have hfa : trace μ (fun x => ((R x).adjoint).adjoint.comp (R x).adjoint)<∞ := by
    simp only [adjoint_adjoint]
    rw [←trace_adjoint_mul hmp R hR hcR]
    exact hf
  have hh := trace_gram_comp_finite_of_bound μ (fun x => (B x).adjoint)
    (fun x => (R x).adjoint) (fun x => by simpa only [adjoint.norm_map] using hb x) hfa
  rw [trace_adjoint_mul hmp _ (matrix_comp_measurable _ _ hBa hRa)
    (covariant_comp _ _ (covariant_adjoint B hcB) (covariant_adjoint R hcR))] at hh
  simpa only [adjoint_comp,adjoint_adjoint] using hh

/-- Weighted finite Gram diagonals are integrable, so their signed traces
may be added and subtracted in the canonical excess calculation. -/
theorem weighted_gram_diagonal_integrable (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (R B : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hR : ∀ g h,Measurable (fun x => matrix (R x) g h))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hcR : Covariant R) (hcB : Covariant B)
    (hf : trace μ (fun x => (R x).adjoint.comp (R x))<∞)
    {C : ℝ} (hb : ∀ x,‖B x‖≤C) :
    Integrable (fun x => (matrix ((B x).comp ((R x).adjoint.comp (R x))) 1 1).re) μ := by
  let T := fun x => (R x).comp (B x).adjoint
  have hT := matrix_comp_measurable R (fun x => (B x).adjoint) hR (matrix_adjoint_measurable B hB)
  have hfT := trace_gram_right_comp_finite μ hmp R (fun x => (B x).adjoint)
    hR (matrix_adjoint_measurable B hB) hcR (covariant_adjoint B hcB) hf
    (fun x => by simpa only [adjoint.norm_map] using hb x)
  have hh := cross_integrable μ T R hT hR (energy_integrable μ T hT hfT)
    (energy_integrable μ R hR hf)
  simpa only [←matrix_cross,T,adjoint_comp,adjoint_adjoint,comp_assoc] using hh

#print axioms signedTrace_weighted_gram_bound
#print axioms trace_gram_right_comp_finite
#print axioms weighted_gram_diagonal_integrable
end AsymptoticRegularTrace
