module

public import AsymptoticRegularSignedTraceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α]

/-- Express the ordinary integral of root-column energy through the
positive rooted trace. -/
theorem energy_integral_eq_toReal (μ : Measure α)
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (B x) g h)) :
    (∫ x,‖B x (delta 1)‖^2 ∂μ)=(trace μ (fun x => (B x).adjoint.comp (B x))).toReal := by
  rw [trace_gram]
  exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => sq_nonneg ‖B x (delta 1)‖))
    (energy_measurable B hm).aestronglyMeasurable

theorem energy_integral_add (μ : Measure α)
    (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hC : ∀ g h,Measurable (fun x => matrix (C x) g h))
    (hb : Integrable (fun x => ‖B x (delta 1)‖^2) μ)
    (hc : Integrable (fun x => ‖C x (delta 1)‖^2) μ) :
    (∫ x,‖(B x+C x) (delta 1)‖^2 ∂μ)=
      (∫ x,‖B x (delta 1)‖^2 ∂μ)+
        2*(∫ x,(⟪B x (delta 1),C x (delta 1)⟫_ℂ).re ∂μ)+(∫ x,‖C x (delta 1)‖^2 ∂μ) := by
  have hi := cross_integrable μ B C hB hC hb hc
  simp only [energy_add]
  have hi2 : Integrable (fun x => 2*(⟪B x (delta 1),C x (delta 1)⟫_ℂ).re) μ := hi.const_mul 2
  have hb2 : Integrable (fun x => ‖B x (delta 1)‖^2+2*(⟪B x (delta 1),C x (delta 1)⟫_ℂ).re) μ := hb.add hi2
  rw [integral_add hb2 hc,integral_add hb hi2,integral_const_mul]

variable [MulAction G α]

theorem energy_integral_adjoint (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (B x) g h)) (hc : Covariant B) :
    (∫ x,‖B x (delta 1)‖^2 ∂μ)=(∫ x,‖(B x).adjoint (delta 1)‖^2 ∂μ) := by
  rw [energy_integral_eq_toReal μ B hm,
    energy_integral_eq_toReal μ (fun x => (B x).adjoint) (matrix_adjoint_measurable B hm)]
  simp only [adjoint_adjoint]
  exact congrArg ENNReal.toReal (trace_adjoint_mul hmp B hm hc)

/-- Real cyclicity for two square-integrable covariant families, obtained
by polarizing the nonnegative Gram identity. Explicit integrability
prevents subtraction of infinite positive traces. -/
theorem signedTrace_adjoint_mul (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hC : ∀ g h,Measurable (fun x => matrix (C x) g h))
    (hb : Covariant B) (hc : Covariant C)
    (hbf : trace μ (fun x => (B x).adjoint.comp (B x))<∞)
    (hcf : trace μ (fun x => (C x).adjoint.comp (C x))<∞) :
    signedTrace μ (fun x => (B x).adjoint.comp (C x))=
      signedTrace μ (fun x => (B x).comp (C x).adjoint) := by
  have hba := matrix_adjoint_measurable B hB
  have hca := matrix_adjoint_measurable C hC
  have hib := energy_integrable μ B hB hbf
  have hic := energy_integrable μ C hC hcf
  have hiba : Integrable (fun x => ‖(B x).adjoint (delta 1)‖^2) μ := by
    apply energy_integrable μ _ hba
    simp only [adjoint_adjoint]
    rw [← trace_adjoint_mul hmp B hB hb]
    exact hbf
  have hica : Integrable (fun x => ‖(C x).adjoint (delta 1)‖^2) μ := by
    apply energy_integrable μ _ hca
    simp only [adjoint_adjoint]
    rw [← trace_adjoint_mul hmp C hC hc]
    exact hcf
  have heB := energy_integral_adjoint μ hmp B hB hb
  have heC := energy_integral_adjoint μ hmp C hC hc
  have heS := energy_integral_adjoint μ hmp (fun x => B x+C x)
    (matrix_add_measurable B C hB hC) (covariant_add B C hb hc)
  simp only [map_add] at heS
  rw [energy_integral_add μ B C hB hC hib hic,
    energy_integral_add μ (fun x => (B x).adjoint) (fun x => (C x).adjoint) hba hca hiba hica] at heS
  have ht : (∫ x,(⟪B x (delta 1),C x (delta 1)⟫_ℂ).re ∂μ)=
      ∫ x,(⟪(B x).adjoint (delta 1),(C x).adjoint (delta 1)⟫_ℂ).re ∂μ := by linarith
  have hg (x : α) : matrix ((B x).comp (C x).adjoint) 1 1=
      ⟪(B x).adjoint (delta 1),(C x).adjoint (delta 1)⟫_ℂ := by
    simpa only [adjoint_adjoint] using matrix_cross (B x).adjoint (C x).adjoint 1
  simpa only [signedTrace,matrix_cross,hg] using ht

#print axioms energy_integral_add
#print axioms energy_integral_adjoint
#print axioms signedTrace_adjoint_mul

end AsymptoticRegularTrace
