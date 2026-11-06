module

public import QuantitativeSpectralRegularCornerStepV1
public import AsymptoticRegularSupportProjectionsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralStepTrace

open MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticPolarIsometry
open QuantitativeSpectralCornerCutRow QuantitativeSpectralCutRow
open QuantitativeSpectralRegularCornerStep
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- Exact rooted trace accounting for a constructed spectral deflation step. -/
theorem removedSpace_trace (μ : Measure α)
    (P : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x, CompleteSpace (P x)]
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmP : ∀ g h, Measurable (fun x => matrix (P x).starProjection g h))
    (hcP : Covariant (fun x => (P x).starProjection))
    (hmB : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hcB : Covariant B)
    (M : ℝ) (hM : ∀ x, ‖B x‖ ≤ M) {c : ℝ} (hc : 0 < c)
    (hf : trace μ (fun x => (P x).starProjection) < ∞) :
    (trace μ (fun x => (removedSpace (P x) (B x) c).starProjection)).toReal =
      (trace μ (fun x => (P x).starProjection)).toReal -
      (trace μ (fun x => (nextSpace (P x) (B x) c).starProjection)).toReal := by
  have hr := (step_regular P B hmP hcP hmB hcB M hM c hc).1
  have he (x : α) : (removedSpace (P x) (B x) c).starProjection =
      (P x).starProjection - (nextSpace (P x) (B x) c).starProjection := by
    rw [nextSpace_projection]
    change removed (restricted (P x) (B x)) c = _
    abel
  have hmR : ∀ g h, Measurable (fun x => matrix (removedSpace (P x) (B x) c).starProjection g h) := by
    simp only [he]
    exact matrix_sub_measurable _ _ hmP hr.1
  have hs (x : α) : ((removedSpace (P x) (B x) c).starProjection).kerᗮ =
      removedSpace (P x) (B x) c := by
    rw [Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]
  have hsp (x : α) : (((removedSpace (P x) (B x) c).starProjection).kerᗮ).starProjection =
      (removedSpace (P x) (B x) c).starProjection := starProjection_congr _ _ (hs x)
  have hh := corner_removed_trace μ P
    (fun x => (removedSpace (P x) (B x) c).starProjection)
    (fun x => Submodule.starProjection_comp_starProjection_of_le (removedSpace_le (P x) (B x) c))
    (by simpa only [hsp] using hmR 1 1) hf
  simp only [hsp] at hh
  simpa only [nextSpace, removed, removedSpace] using hh

#print axioms removedSpace_trace

end QuantitativeSpectralStepTrace
