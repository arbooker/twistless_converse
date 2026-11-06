module

public import AsymptoticPolarIsometryV1
public import AsymptoticRegularTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPolarIsometry

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

noncomputable def outputSpace (T : H →L[ℂ] J) : Submodule ℂ J := T.range.topologicalClosure

noncomputable instance outputSpace_complete (T : H →L[ℂ] J) : CompleteSpace (outputSpace T) :=
  T.range.isClosed_topologicalClosure.completeSpace_coe

theorem rangeIsometry_range (T : H →L[ℂ] J) (S : H →L[ℂ] H)
    (h : ∀ x,‖T x‖=‖S x‖) : (rangeIsometry T S h).toContinuousLinearMap.range=outputSpace T := by
  let V := rangeIsometry T S h
  have hc : IsClosed (V.toContinuousLinearMap.range : Set J) :=
    V.isometry.isClosedEmbedding.isClosed_range
  apply le_antisymm
  · rintro _ ⟨y,rfl⟩
    refine (rangeMap_dense S).induction_on (p:=fun y => V y∈outputSpace T) y
      (T.range.isClosed_topologicalClosure.preimage V.continuous) ?_
    intro x
    change rangeIsometry T S h (rangeMap S x)∈outputSpace T
    rw [rangeIsometry_map]
    exact T.range.le_topologicalClosure ⟨x,rfl⟩
  · apply T.range.topologicalClosure_minimal _ hc
    rintro _ ⟨x,rfl⟩
    exact ⟨rangeMap S x,rangeIsometry_map T S h x⟩

/-- The range isometry identifies the output support projection even
when the range of the original operator is not closed. -/
theorem rangeIsometry_cogram (T : H →L[ℂ] J) (S : H →L[ℂ] H)
    (h : ∀ x,‖T x‖=‖S x‖) :
    (rangeIsometry T S h).toContinuousLinearMap.comp (rangeIsometry T S h).toContinuousLinearMap.adjoint=
      (outputSpace T).starProjection := by
  let V := (rangeIsometry T S h).toContinuousLinearMap
  have hr : V.range=outputSpace T := rangeIsometry_range T S h
  have hg : V.adjoint.comp V=1 := (rangeIsometry T S h).adjoint_comp_self
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← hr]
    exact ⟨V.adjoint x,rfl⟩
  · intro y hy
    rw [← hr] at hy
    obtain ⟨z,rfl⟩ := hy
    change ⟪x-V (V.adjoint x),V z⟫_ℂ=0
    rw [← V.adjoint_inner_left,map_sub]
    have he := congrArg (fun B : closedRange S →L[ℂ] closedRange S => B (V.adjoint x)) hg
    change V.adjoint (V (V.adjoint x))=V.adjoint x at he
    rw [he,sub_self,inner_zero_left]

theorem partialIsometry_cogram (T : H →L[ℂ] J) (S : H →L[ℂ] H)
    (h : ∀ x,‖T x‖=‖S x‖) :
    (partialIsometry T S h).comp (partialIsometry T S h).adjoint=(outputSpace T).starProjection := by
  let V := (rangeIsometry T S h).toContinuousLinearMap
  let P := (closedRange S).orthogonalProjectionOnto
  have he : P.comp P.adjoint=1 := by
    rw [show P.adjoint=(closedRange S).subtypeL from (closedRange S).adjoint_orthogonalProjectionOnto]
    apply ContinuousLinearMap.ext
    intro x
    exact (closedRange S).orthogonalProjectionOnto_mem_subspace_eq_self x
  change (V.comp P).comp (V.comp P).adjoint=_
  rw [adjoint_comp,comp_assoc,← comp_assoc P P.adjoint V.adjoint,he,one_def,id_comp]
  exact rangeIsometry_cogram T S h

theorem polar_cogram (T : H →L[ℂ] J) :
    (polar T).comp (polar T).adjoint=(outputSpace T).starProjection :=
  partialIsometry_cogram T (absolute T) (absolute_norm T)

#print axioms rangeIsometry_range
#print axioms rangeIsometry_cogram
#print axioms partialIsometry_cogram
#print axioms polar_cogram

end AsymptoticPolarIsometry

namespace AsymptoticRegularTrace

open MeasureTheory AsymptoticPolarIsometry
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- Measurable covariant polar decompositions equate the two support
trace dimensions. No closed-range or finite-trace assumption is needed
for this extended-real identity. -/
theorem support_trace_eq_of_polar_covariant (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (polar (T x)) g h))
    (hc : Covariant (fun x => polar (T x))) :
    trace μ (fun x => (T x).kerᗮ.starProjection)=
      trace μ (fun x => (outputSpace (T x)).starProjection) := by
  have ht := trace_adjoint_mul hmp (fun x => polar (T x)) hm hc
  simpa only [polar_gram,polar_cogram] using ht

#print axioms support_trace_eq_of_polar_covariant

end AsymptoticRegularTrace
