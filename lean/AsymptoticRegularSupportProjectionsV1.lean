module

public import AsymptoticRankMonotonicityV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPolarIsometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem starProjection_congr (U V : Submodule ℂ H) [CompleteSpace U] [CompleteSpace V]
    (hUV : U=V) : U.starProjection=V.starProjection := by
  subst V
  rfl

#print axioms starProjection_congr

end AsymptoticPolarIsometry

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap AsymptoticPolarIsometry AsymptoticCornerKernel
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

theorem source_support_regular (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M) :
    (∀ g h,Measurable (fun x => matrix (T x).kerᗮ.starProjection g h)) ∧
      Covariant (fun x => (T x).kerᗮ.starProjection) := by
  obtain ⟨hp,hcp⟩ := polar_regular T hm hc M hM
  have hm' := matrix_comp_measurable _ _
    (matrix_adjoint_measurable (fun x => polar (T x)) hp) hp
  have hc' := covariant_comp _ _ (covariant_adjoint _ hcp) hcp
  simpa only [polar_gram] using And.intro hm' hc'

theorem output_support_regular (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M) :
    (∀ g h,Measurable (fun x => matrix (outputSpace (T x)).starProjection g h)) ∧
      Covariant (fun x => (outputSpace (T x)).starProjection) := by
  obtain ⟨hp,hcp⟩ := polar_regular T hm hc M hM
  have hm' := matrix_comp_measurable _ _ hp
    (matrix_adjoint_measurable (fun x => polar (T x)) hp)
  have hc' := covariant_comp _ _ hcp (covariant_adjoint _ hcp)
  simpa only [polar_cogram] using And.intro hm' hc'

/-- Intersecting a regular closed source with the kernel of a bounded
regular observation preserves measurability and covariance. -/
theorem remaining_regular (P : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (P x)]
    (hP : ∀ g h,Measurable (fun x => matrix (P x).starProjection g h))
    (hcP : Covariant (fun x => (P x).starProjection))
    (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M) :
    (∀ g h,Measurable (fun x => matrix (remaining (P x) (T x)).starProjection g h)) ∧
      Covariant (fun x => (remaining (P x) (T x)).starProjection) := by
  let R := fun x => (T x).comp (P x).starProjection
  have hR := source_support_regular R (matrix_comp_measurable _ _ hm hP)
    (covariant_comp _ _ hc hcP) M (fun x => (restricted_norm_le (P x) (T x)).trans (hM x))
  have he (x : α) : (remaining (P x) (T x)).starProjection=
      (P x).starProjection-(R x).kerᗮ.starProjection := by
    exact (starProjection_congr _ _ (remaining_restricted (P x) (T x)).symm).trans
      (remaining_projection (P x) (R x) (restricted_comp_projection (P x) (T x)))
  simp only [he]
  exact ⟨matrix_sub_measurable _ _ hP hR.1,covariant_sub _ _ hcP hR.2⟩

#print axioms source_support_regular
#print axioms output_support_regular
#print axioms remaining_regular

end AsymptoticRegularTrace
