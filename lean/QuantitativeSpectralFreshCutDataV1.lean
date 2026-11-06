module

public import QuantitativeSpectralCutWhiteningV1
public import QuantitativeSpectralRegularRowV1
public import QuantitativeSpectralFreshPolarV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralFreshCutData

open MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticObservationStack
open AsymptoticPolarIsometry AsymptoticSubgroupSupport QuantitativeSpectralCutPolar
open QuantitativeSpectralCutWhitening QuantitativeSpectralCutRegularity
open scoped lp

variable {G α ι : Type*} [Group G] [Countable G] [Fintype ι]
  [MeasurableSpace α] [MulAction G α]

def cutRows (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (c : ℝ) (i : ι) :
    ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) := (L i).comp (cutSpace (stack L) c).starProjection

omit [Group G] [Countable G] in
theorem stack_cutRows (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (c : ℝ) :
    stack (cutRows L c) = cutOperator (stack L) c := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  rfl

omit [Group G] [Countable G] in
theorem cutRows_norm (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (c : ℝ) :
    ‖stack (cutRows L c)‖ ≤ ‖stack L‖ := by
  rw [stack_cutRows]
  exact (opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_left
    (cutSpace (stack L) c).starProjection_norm_le (norm_nonneg (stack L))).trans_eq (mul_one _))

theorem cutProjection_regular
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h, Measurable (fun x => matrix (L x i) g h))
    (hc : ∀ i, Covariant (fun x => L x i)) (M : ℝ) (hM : ∀ x, ‖stack (L x)‖ ≤ M) (c : ℝ) :
    (∀ g h, Measurable (fun x => matrix (cutSpace (stack (L x)) c).starProjection g h)) ∧
      Covariant (fun x => (cutSpace (stack (L x)) c).starProjection) := by
  have hr := stack_gram_regular L hm hc
  apply highAt_regular _ hr.1 hr.2 _ (M^2) _ (c^2)
  · intro x
    rw [isSelfAdjoint_iff']
    simp only [adjoint_comp, adjoint_adjoint]
  · intro x
    rw [norm_adjoint_comp_self]
    nlinarith [hM x, norm_nonneg (stack (L x))]

theorem cutRows_regular
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h, Measurable (fun x => matrix (L x i) g h))
    (hc : ∀ i, Covariant (fun x => L x i)) (M : ℝ) (hM : ∀ x, ‖stack (L x)‖ ≤ M)
    (c : ℝ) (i : ι) :
    (∀ g h, Measurable (fun x => matrix (cutRows (L x) c i) g h)) ∧
      Covariant (fun x => cutRows (L x) c i) := by
  have hr := cutProjection_regular L hm hc M hM c
  exact ⟨matrix_comp_measurable _ _ (hm i) hr.1, covariant_comp _ _ (hc i) hr.2⟩

omit [Countable G] [MeasurableSpace α] [MulAction G α] in
theorem cutRows_supported (S : Subgroup G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hL : ∀ i, Supported S (L i)) (c : ℝ) (i : ι) : Supported S (cutRows L c i) := by
  apply supported_comp S _ _ (hL i)
  apply highAt_supported S _ (supported_stackGram S L hL)
  rw [isSelfAdjoint_iff']
  simp only [adjoint_comp, adjoint_adjoint]

theorem cutWhitening_regular
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h, Measurable (fun x => matrix (L x i) g h))
    (hc : ∀ i, Covariant (fun x => L x i)) (M : ℝ) (hM : ∀ x, ‖stack (L x)‖ ≤ M)
    {c : ℝ} (hcpos : 0 < c) :
    (∀ g h, Measurable (fun x => matrix (cutWhitening (stack (L x)) c) g h)) ∧
      Covariant (fun x => cutWhitening (stack (L x)) c) := by
  have hr := cutProjection_regular L hm hc M hM c
  have hl := cutRows_regular L hm hc M hM c
  have hb := stack_absolute_regular (fun x => cutRows (L x) c)
    (fun i => (hl i).1) (fun i => (hl i).2) M
    (fun x => (cutRows_norm (L x) c).trans (hM x))
  simp only [stack_cutRows] at hb
  have hn := QuantitativeSpectralRegularRow.normalizer_regular
    (fun x => (cutSpace (stack (L x)) c).starProjection)
    (fun x => absolute (cutOperator (stack (L x)) c)) hr.1 hr.2 hb.1 hb.2
    (fun x => ⟨Submodule.isIdempotentElem_starProjection _,
      isSelfAdjoint_iff'.mpr (isSelfAdjoint_starProjection _)⟩) c hcpos
    (fun x => absolute_cut_coercive (stack (L x)) c) M (fun x => by
      rw [absolute_opNorm]
      exact (show ‖cutOperator (stack (L x)) c‖ ≤ ‖stack (L x)‖ from
        (stack_cutRows (L x) c) ▸ cutRows_norm (L x) c).trans (hM x))
  exact ⟨matrix_smul_measurable ((c⁻¹:ℝ):ℂ) _ (matrix_adjoint_measurable _ hn.1),
    covariant_smul ((c⁻¹:ℝ):ℂ) _ (covariant_adjoint _ hn.2)⟩

#print axioms stack_cutRows
#print axioms cutProjection_regular
#print axioms cutRows_regular
#print axioms cutRows_supported
#print axioms cutWhitening_regular

end QuantitativeSpectralFreshCutData
