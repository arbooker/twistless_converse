module

public import AsymptoticRankRestrictionV1
public import AsymptoticRegularPolarV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticPolarIsometry

open ContinuousLinearMap

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

omit [CompleteSpace H] [CompleteSpace J] in
theorem restricted_output_mono (P Q : Submodule ℂ H)
    [CompleteSpace P] [CompleteSpace Q] (hPQ : P≤Q) (T : H →L[ℂ] J) :
    outputSpace (T.comp P.starProjection)≤outputSpace (T.comp Q.starProjection) := by
  apply Submodule.topologicalClosure_mono
  rintro _ ⟨v,rfl⟩
  refine ⟨P.starProjection v,?_⟩
  change T (Q.starProjection (P.starProjection v))=T (P.starProjection v)
  rw [Q.starProjection_eq_self_iff.mpr (hPQ (P.starProjection_apply_mem v))]

omit [CompleteSpace H] [CompleteSpace J] in
theorem restricted_norm_le (P : Submodule ℂ H) [CompleteSpace P] (T : H →L[ℂ] J) :
    ‖T.comp P.starProjection‖≤‖T‖ := by
  calc
    _≤‖T‖*‖P.starProjection‖ := opNorm_comp_le _ _
    _≤‖T‖*1 := mul_le_mul_of_nonneg_left P.starProjection_norm_le (norm_nonneg T)
    _=‖T‖ := mul_one _

#print axioms restricted_output_mono
#print axioms restricted_norm_le

end AsymptoticPolarIsometry

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap AsymptoticPolarIsometry
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- Rank increases with the source corner. Source supports need not be
ordered; comparing closed output ranges and using the polar trace
identity gives the required monotonicity. -/
theorem restricted_rank_mono (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (P Q : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ x,CompleteSpace (P x)] [∀ x,CompleteSpace (Q x)] (hPQ : ∀ x,P x≤Q x)
    (hmP : ∀ g h,Measurable (fun x => matrix (P x).starProjection g h))
    (hmQ : ∀ g h,Measurable (fun x => matrix (Q x).starProjection g h))
    (hcP : Covariant (fun x => (P x).starProjection))
    (hcQ : Covariant (fun x => (Q x).starProjection))
    (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M) :
    trace μ (fun x => ((T x).comp (P x).starProjection).kerᗮ.starProjection)≤
      trace μ (fun x => ((T x).comp (Q x).starProjection).kerᗮ.starProjection) := by
  rw [support_trace_eq μ hmp _ (matrix_comp_measurable _ _ hm hmP)
    (covariant_comp _ _ hc hcP) M (fun x => (restricted_norm_le (P x) (T x)).trans (hM x))]
  rw [support_trace_eq μ hmp _ (matrix_comp_measurable _ _ hm hmQ)
    (covariant_comp _ _ hc hcQ) M (fun x => (restricted_norm_le (Q x) (T x)).trans (hM x))]
  exact projection_trace_mono μ _ _ (fun x => restricted_output_mono (P x) (Q x) (hPQ x) (T x))

/-- Faithfulness detects a zero rank without an injectivity or
closed-range assumption. -/
theorem ae_zero_of_support_trace_zero (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M)
    (hz : trace μ (fun x => (T x).kerᗮ.starProjection)=0) : ∀ᵐ x ∂μ,T x=0 := by
  have hp := polar_regular T hm hc M hM
  have hgram : trace μ (fun x => (polar (T x)).adjoint.comp (polar (T x)))=0 := by
    simpa only [polar_gram] using hz
  have hae := trace_gram_faithful hmp (fun x => polar (T x)) (fun g => hp.1 g 1) hp.2 hgram
  filter_upwards [hae] with x hx
  rw [← polar_factor (T x),hx,zero_comp]

#print axioms restricted_rank_mono
#print axioms ae_zero_of_support_trace_zero

end AsymptoticRegularTrace
