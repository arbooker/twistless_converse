module

public import AsymptoticDecreasingProjectionTraceV1
public import AsymptoticRegularTraceSandwichV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap
open scoped lp ENNReal

variable {G α : Type*} [Group G] [MeasurableSpace α]

theorem projection_trace_mono (μ : Measure α)
    (U V : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (U x)] [∀ x,CompleteSpace (V x)]
    (hUV : ∀ x,U x≤V x) :
    trace μ (fun x => (U x).starProjection)≤trace μ (fun x => (V x).starProjection) := by
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  rw [projection_root_eq_norm,projection_root_eq_norm]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (AsymptoticStrongConvergence.projection_norm_le_of_le _ _ (hUV x) (delta 1)) 2

theorem projection_trace_finite_of_le (μ : Measure α)
    (U V : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (U x)] [∀ x,CompleteSpace (V x)]
    (hUV : ∀ x,U x≤V x) (hf : trace μ (fun x => (V x).starProjection)<∞) :
    trace μ (fun x => (U x).starProjection)<∞ :=
  (projection_trace_mono μ U V hUV).trans_lt hf

theorem projection_signedTrace (μ : Measure α)
    (U : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (U x)]
    (hm : Measurable (fun x => matrix (U x).starProjection 1 1)) :
    signedTrace μ (fun x => (U x).starProjection)=
      (trace μ (fun x => (U x).starProjection)).toReal := by
  apply integral_eq_lintegral_of_nonneg_ae
  · exact Filter.Eventually.of_forall (fun x => by
      change (0:ℝ)≤(matrix (U x).starProjection 1 1).re
      rw [projection_root_eq_norm]
      positivity)
  · exact (Complex.continuous_re.measurable.comp hm).aestronglyMeasurable

variable [Countable G] [MulAction G α]

/-- A measurable covariant square-integrable pair is cyclic for the real
rooted trace. This form applies directly to bounded inverse embeddings. -/
theorem signedTrace_comp_comm (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hC : ∀ g h,Measurable (fun x => matrix (C x) g h))
    (hcB : Covariant B) (hcC : Covariant C)
    (hb : trace μ (fun x => (B x).adjoint.comp (B x))<∞)
    (hc : trace μ (fun x => (C x).adjoint.comp (C x))<∞) :
    signedTrace μ (fun x => (B x).comp (C x))=
      signedTrace μ (fun x => (C x).comp (B x)) := by
  have hba := matrix_adjoint_measurable B hB
  have hbf : trace μ (fun x => ((B x).adjoint).adjoint.comp (B x).adjoint)<∞ := by
    simp only [adjoint_adjoint]
    rw [← trace_adjoint_mul hmp B hB hcB]
    exact hb
  have ht := signedTrace_adjoint_mul μ hmp (fun x => (B x).adjoint) C hba hC
    (covariant_adjoint B hcB) hcC hbf hc
  simp only [adjoint_adjoint] at ht
  have ha := signedTrace_adjoint μ (fun x => (C x).comp (B x))
  simp only [adjoint_comp] at ha
  exact ht.trans ha

/-- Closed module subspaces related by bounded inverse embeddings have
identical finite trace dimensions. The embeddings and all measurability
and covariance requirements are explicit. -/
theorem projection_trace_eq_of_inverse_embeddings (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (U V : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (U x)] [∀ x,CompleteSpace (V x)]
    (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hC : ∀ g h,Measurable (fun x => matrix (C x) g h))
    (hcB : Covariant B) (hcC : Covariant C)
    (hb : trace μ (fun x => (B x).adjoint.comp (B x))<∞)
    (hc : trace μ (fun x => (C x).adjoint.comp (C x))<∞)
    (hBC : ∀ x,(B x).comp (C x)=(V x).starProjection)
    (hCB : ∀ x,(C x).comp (B x)=(U x).starProjection)
    (hu : trace μ (fun x => (U x).starProjection)<∞)
    (hv : trace μ (fun x => (V x).starProjection)<∞) :
    trace μ (fun x => (U x).starProjection)=trace μ (fun x => (V x).starProjection) := by
  have hmU : Measurable (fun x => matrix (U x).starProjection 1 1) := by
    simpa only [hCB] using matrix_comp_measurable C B hC hB 1 1
  have hmV : Measurable (fun x => matrix (V x).starProjection 1 1) := by
    simpa only [hBC] using matrix_comp_measurable B C hB hC 1 1
  have ht := signedTrace_comp_comm μ hmp B C hB hC hcB hcC hb hc
  simp only [hBC,hCB,projection_signedTrace μ U hmU,projection_signedTrace μ V hmV] at ht
  exact (ENNReal.toReal_eq_toReal_iff' hu.ne hv.ne).mp ht.symm

#print axioms projection_trace_mono
#print axioms projection_trace_finite_of_le
#print axioms projection_signedTrace
#print axioms signedTrace_comp_comm
#print axioms projection_trace_eq_of_inverse_embeddings

end AsymptoticRegularTrace
