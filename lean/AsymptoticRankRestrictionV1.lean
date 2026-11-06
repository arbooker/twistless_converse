module

public import AsymptoticCornerKernelV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCornerKernel

open ContinuousLinearMap

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J]

omit [CompleteSpace H] in
theorem restricted_comp_projection (P : Submodule ℂ H) [CompleteSpace P]
    (T : H →L[ℂ] J) :
    (T.comp P.starProjection).comp P.starProjection=T.comp P.starProjection := by
  have hp : P.starProjection.comp P.starProjection=P.starProjection :=
    P.isIdempotentElem_starProjection
  rw [comp_assoc,hp]

omit [CompleteSpace H] in
theorem remaining_restricted (P : Submodule ℂ H) [CompleteSpace P]
    (T : H →L[ℂ] J) : remaining P (T.comp P.starProjection)=remaining P T := by
  ext v
  change (v∈P ∧ T (P.starProjection v)=0) ↔ (v∈P ∧ T v=0)
  constructor
  · rintro ⟨hp,ht⟩
    exact ⟨hp,by simpa only [P.starProjection_eq_self_iff.mpr hp] using ht⟩
  · rintro ⟨hp,ht⟩
    exact ⟨hp,by simpa only [P.starProjection_eq_self_iff.mpr hp] using ht⟩

#print axioms restricted_comp_projection
#print axioms remaining_restricted

end AsymptoticCornerKernel

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap AsymptoticCornerKernel
open scoped lp ENNReal

variable {G α J : Type*} [Group G] [MeasurableSpace α]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J]

/-- Restricting an observation to a smaller finite corner lowers its
rank by at most the trace removed from the corner. This applies to a
whole labelled stack, with no closed-range requirement. -/
theorem rank_restriction (μ : Measure α)
    (P Q : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ x,CompleteSpace (P x)] [∀ x,CompleteSpace (Q x)]
    (hQP : ∀ x,Q x≤P x) (T : α → ℓ²(G,ℂ) →L[ℂ] J)
    (hP : Measurable (fun x => matrix ((T x).comp (P x).starProjection).kerᗮ.starProjection 1 1))
    (hQ : Measurable (fun x => matrix ((T x).comp (Q x).starProjection).kerᗮ.starProjection 1 1))
    (hf : trace μ (fun x => (P x).starProjection)<∞) :
    (trace μ (fun x => ((T x).comp (P x).starProjection).kerᗮ.starProjection)).toReal≤
      (trace μ (fun x => ((T x).comp (Q x).starProjection).kerᗮ.starProjection)).toReal+
        ((trace μ (fun x => (P x).starProjection)).toReal-
          (trace μ (fun x => (Q x).starProjection)).toReal) := by
  have hqf := projection_trace_finite_of_le μ Q P hQP hf
  have heP := corner_removed_trace μ P (fun x => (T x).comp (P x).starProjection)
    (fun x => restricted_comp_projection (P x) (T x)) hP hf
  have heQ := corner_removed_trace μ Q (fun x => (T x).comp (Q x).starProjection)
    (fun x => restricted_comp_projection (Q x) (T x)) hQ hqf
  simp only [remaining_restricted] at heP heQ
  have hrf := projection_trace_finite_of_le μ (fun x => remaining (P x) (T x)) P
    (fun _ => inf_le_left) hf
  have hmono := projection_trace_mono μ (fun x => remaining (Q x) (T x))
    (fun x => remaining (P x) (T x)) (fun x => inf_le_inf (hQP x) le_rfl)
  have hr := ENNReal.toReal_mono hrf.ne hmono
  linarith

#print axioms rank_restriction

end AsymptoticRegularTrace
