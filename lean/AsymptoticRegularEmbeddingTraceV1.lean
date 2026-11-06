module

public import AsymptoticRegularSupportProjectionsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPolarIsometry

open ContinuousLinearMap

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

omit [CompleteSpace H] [CompleteSpace J] in
/-- Injectivity on a closed source identifies the source support of
the restricted operator. No closed output range is required. -/
theorem restricted_source_of_injective (U : Submodule ℂ H) [CompleteSpace U]
    (B : H →L[ℂ] J) (hinj : ∀ v∈U,B v=0 → v=0) :
    (B.comp U.starProjection).kerᗮ=U := by
  have hk : (B.comp U.starProjection).ker=Uᗮ := by
    ext v
    change B (U.starProjection v)=0 ↔ v∈Uᗮ
    constructor
    · intro hv
      exact U.starProjection_apply_eq_zero_iff.mp
        (hinj _ (U.starProjection_apply_mem v) hv)
    · intro hv
      rw [U.starProjection_apply_eq_zero_iff.mpr hv,map_zero]
  rw [hk,Submodule.orthogonal_orthogonal]

omit [CompleteSpace H] [CompleteSpace J] in
theorem restricted_output_le (U : Submodule ℂ H) [CompleteSpace U]
    (V : Submodule ℂ J) [CompleteSpace V] (B : H →L[ℂ] J)
    (hmap : ∀ v∈U,B v∈V) : outputSpace (B.comp U.starProjection)≤V := by
  apply (B.comp U.starProjection).range.topologicalClosure_minimal
  · rintro _ ⟨v,rfl⟩
    exact hmap _ (U.starProjection_apply_mem v)
  · exact (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace V)).isClosed

#print axioms restricted_source_of_injective
#print axioms restricted_output_le

end AsymptoticPolarIsometry

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap AsymptoticPolarIsometry
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- A bounded regular map injective on a regular closed source cannot
increase trace dimension. This includes maps without bounded inverses
or closed ranges, and allows infinite trace. -/
theorem trace_le_of_injective_map (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (U V : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ x,CompleteSpace (U x)] [∀ x,CompleteSpace (V x)]
    (hmU : ∀ g h,Measurable (fun x => matrix (U x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection))
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmB : ∀ g h,Measurable (fun x => matrix (B x) g h)) (hcB : Covariant B)
    (M : ℝ) (hM : ∀ x,‖B x‖≤M)
    (hinj : ∀ x v,v∈U x → B x v=0 → v=0)
    (hmap : ∀ x v,v∈U x → B x v∈V x) :
    trace μ (fun x => (U x).starProjection)≤trace μ (fun x => (V x).starProjection) := by
  let T := fun x => (B x).comp (U x).starProjection
  have ht := support_trace_eq μ hmp T (matrix_comp_measurable _ _ hmB hmU)
    (covariant_comp _ _ hcB hcU) M (fun x => (restricted_norm_le (U x) (B x)).trans (hM x))
  have he (x : α) : (T x).kerᗮ=U x := restricted_source_of_injective (U x) (B x) (hinj x)
  have hr := projection_trace_mono μ (fun x => outputSpace (T x)) V
    (fun x => restricted_output_le (U x) (V x) (B x) (hmap x))
  have hleft : trace μ (fun x => (T x).kerᗮ.starProjection)=
      trace μ (fun x => (U x).starProjection) := by
    congr 1
    funext x
    exact starProjection_congr _ _ (he x)
  rw [hleft] at ht
  exact ht.le.trans hr

#print axioms trace_le_of_injective_map

end AsymptoticRegularTrace
