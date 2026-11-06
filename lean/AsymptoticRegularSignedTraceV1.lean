module

public import AsymptoticRegularAlgebraV1
public import AsymptoticRegularNormalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped lp ENNReal

variable {G α : Type*} [Group G] [MeasurableSpace α]

/-- The real integral of the rooted diagonal. For positive families it
agrees with the finite positive trace; integrability is stated explicitly
whenever linearity of this signed extension is used. -/
noncomputable def signedTrace (μ : Measure α) (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) : ℝ :=
  ∫ x,(matrix (B x) 1 1).re ∂μ

theorem signedTrace_eq_toReal (μ : Measure α) (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : Measurable (fun x => matrix (B x) 1 1)) (hp : ∀ x,(B x).IsPositive) :
    signedTrace μ B=(trace μ B).toReal :=
  integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => root_nonneg _ (hp x)))
    (Complex.continuous_re.measurable.comp hm).aestronglyMeasurable

omit [Group G] in
theorem matrix_adjoint_measurable (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (B x) g h)) (g h : G) :
    Measurable (fun x => matrix (B x).adjoint g h) := by
  simp only [matrix_adjoint]
  exact Complex.continuous_conj.measurable.comp (hm h g)

omit [Group G] in
theorem matrix_cross (B C : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (g : G) :
    matrix (B.adjoint.comp C) g g=⟪B (delta g),C (delta g)⟫_ℂ := by
  rw [matrix,← delta_inner,comp_apply,adjoint_inner_right]

theorem energy_measurable [Countable G] (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (B x) g h)) :
    Measurable (fun x => ‖B x (delta 1)‖^2) := by
  have hg := Complex.continuous_re.measurable.comp
    (matrix_comp_measurable _ _ (matrix_adjoint_measurable B hm) hm 1 1)
  simpa only [Function.comp_def,matrix_gram] using hg

theorem energy_integrable [Countable G] (μ : Measure α)
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hf : trace μ (fun x => (B x).adjoint.comp (B x))<∞) :
    Integrable (fun x => ‖B x (delta 1)‖^2) μ := by
  refine ⟨(energy_measurable B hm).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun x => sq_nonneg ‖B x (delta 1)‖))).mpr
  exact (trace_gram μ B).symm ▸ hf

theorem cross_integrable [Countable G] (μ : Measure α)
    (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hC : ∀ g h,Measurable (fun x => matrix (C x) g h))
    (hb : Integrable (fun x => ‖B x (delta 1)‖^2) μ)
    (hc : Integrable (fun x => ‖C x (delta 1)‖^2) μ) :
    Integrable (fun x => (⟪B x (delta 1),C x (delta 1)⟫_ℂ).re) μ := by
  have hm := Complex.continuous_re.measurable.comp
    (matrix_comp_measurable _ _ (matrix_adjoint_measurable B hB) hC 1 1)
  simp only [matrix_cross] at hm
  apply (hb.add hc).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_inner_le_norm (B x (delta 1)) (C x (delta 1))).trans
  change ‖B x (delta 1)‖*‖C x (delta 1)‖≤‖B x (delta 1)‖^2+‖C x (delta 1)‖^2
  nlinarith [sq_nonneg (‖B x (delta 1)‖-‖C x (delta 1)‖),sq_nonneg ‖B x (delta 1)‖,sq_nonneg ‖C x (delta 1)‖]

theorem energy_add (B C : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) :
    ‖(B+C) (delta 1)‖^2=‖B (delta 1)‖^2+2*(⟪B (delta 1),C (delta 1)⟫_ℂ).re+‖C (delta 1)‖^2 :=
  norm_add_sq (𝕜:=ℂ) _ _

#print axioms signedTrace_eq_toReal
#print axioms energy_integrable
#print axioms cross_integrable

end AsymptoticRegularTrace
