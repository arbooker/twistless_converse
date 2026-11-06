module

public import AsymptoticRegularSupportProjectionsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticSubspaceIntersection

open ContinuousLinearMap AsymptoticCornerKernel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def inter (U V : Submodule ℂ H) [CompleteSpace V] : Submodule ℂ H :=
  remaining U (1-V.starProjection)

noncomputable instance inter_complete (U V : Submodule ℂ H) [CompleteSpace U] [CompleteSpace V] :
    CompleteSpace (inter U V) := inferInstanceAs (CompleteSpace (remaining U (1-V.starProjection)))

omit [CompleteSpace H] in
theorem inter_mem (U V : Submodule ℂ H) [CompleteSpace V] (v : H) :
    v∈inter U V ↔ v∈U ∧ v∈V := by
  change (v∈U ∧ v-V.starProjection v=0) ↔ _
  constructor
  · rintro ⟨hu,hv⟩
    exact ⟨hu,V.starProjection_eq_self_iff.mp (sub_eq_zero.mp hv).symm⟩
  · rintro ⟨hu,hv⟩
    exact ⟨hu,sub_eq_zero.mpr (V.starProjection_eq_self_iff.mpr hv).symm⟩

omit [CompleteSpace H] in
theorem inter_eq_left (U V : Submodule ℂ H) [CompleteSpace V] (hUV : U≤V) : inter U V=U := by
  ext v
  rw [inter_mem]
  exact ⟨And.left,fun hv => ⟨hv,hUV hv⟩⟩

#print axioms inter_mem
#print axioms inter_eq_left

end AsymptoticSubspaceIntersection

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap AsymptoticSubspaceIntersection AsymptoticPolarIsometry
open scoped lp

variable {G α : Type*} [Group G] [MeasurableSpace α]

theorem trace_inter_eq_of_ae_le (μ : Measure α)
    (U V : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (U x)] [∀ x,CompleteSpace (V x)]
    (hUV : ∀ᵐ x ∂μ,U x≤V x) :
    trace μ (fun x => (inter (U x) (V x)).starProjection)=trace μ (fun x => (U x).starProjection) := by
  apply lintegral_congr_ae
  filter_upwards [hUV] with x hx
  rw [starProjection_congr _ _ (inter_eq_left (U x) (V x) hx)]

variable [Countable G] [MulAction G α]

theorem inter_regular (U V : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ x,CompleteSpace (U x)] [∀ x,CompleteSpace (V x)]
    (hmU : ∀ g h,Measurable (fun x => matrix (U x).starProjection g h))
    (hmV : ∀ g h,Measurable (fun x => matrix (V x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection))
    (hcV : Covariant (fun x => (V x).starProjection)) :
    (∀ g h,Measurable (fun x => matrix (inter (U x) (V x)).starProjection g h)) ∧
      Covariant (fun x => (inter (U x) (V x)).starProjection) := by
  apply remaining_regular U hmU hcU (fun x => 1-(V x).starProjection)
    (matrix_sub_measurable _ _ (fun _ _ => measurable_const) hmV)
    (covariant_sub _ _ covariant_one hcV) 2
  intro x
  have hV := (V x).starProjection_norm_le
  have h1 : ‖(1:ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))‖≤1 := norm_id_le
  exact (norm_sub_le _ _).trans (by linarith)

#print axioms trace_inter_eq_of_ae_le
#print axioms inter_regular

end AsymptoticRegularTrace
