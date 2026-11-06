module

public import AsymptoticRegularEmbeddingTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap AsymptoticCornerKernel AsymptoticPolarIsometry
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- Cutting a regular subspace loses no more trace than cutting its
finite ambient space. The cut may be any bounded regular observation. -/
theorem remaining_trace_deficit (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (U S : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ x,CompleteSpace (U x)] [∀ x,CompleteSpace (S x)]
    (hUS : ∀ x,U x≤S x)
    (hmU : ∀ g h,Measurable (fun x => matrix (U x).starProjection g h))
    (hmS : ∀ g h,Measurable (fun x => matrix (S x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection))
    (hcS : Covariant (fun x => (S x).starProjection))
    (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmT : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hcT : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M)
    (hfin : trace μ (fun x => (S x).starProjection)<∞) :
    (trace μ (fun x => (U x).starProjection)).toReal≤
      (trace μ (fun x => (remaining (U x) (T x)).starProjection)).toReal+
        ((trace μ (fun x => (S x).starProjection)).toReal-
          (trace μ (fun x => (remaining (S x) (T x)).starProjection)).toReal) := by
  have huf := projection_trace_finite_of_le μ U S hUS hfin
  have hrU := source_support_regular (fun x => (T x).comp (U x).starProjection)
    (matrix_comp_measurable _ _ hmT hmU) (covariant_comp _ _ hcT hcU)
    M (fun x => (restricted_norm_le (U x) (T x)).trans (hM x))
  have hrS := source_support_regular (fun x => (T x).comp (S x).starProjection)
    (matrix_comp_measurable _ _ hmT hmS) (covariant_comp _ _ hcT hcS)
    M (fun x => (restricted_norm_le (S x) (T x)).trans (hM x))
  have heU := corner_removed_trace μ U (fun x => (T x).comp (U x).starProjection)
    (fun x => restricted_comp_projection (U x) (T x)) (hrU.1 1 1) huf
  have heS := corner_removed_trace μ S (fun x => (T x).comp (S x).starProjection)
    (fun x => restricted_comp_projection (S x) (T x)) (hrS.1 1 1) hfin
  simp only [remaining_restricted] at heU heS
  have hm := restricted_rank_mono μ hmp U S hUS hmU hmS hcU hcS T hmT hcT M hM
  have hsf := projection_trace_finite_of_le μ
    (fun x => ((T x).comp (S x).starProjection).kerᗮ) S
    (fun x => support_le (S x) _ (restricted_comp_projection (S x) (T x))) hfin
  have hl := ENNReal.toReal_mono hsf.ne hm
  linarith

#print axioms remaining_trace_deficit

end AsymptoticRegularTrace
