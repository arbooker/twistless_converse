module

public import AsymptoticQuotientProductV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticQuotientOperators

open AsymptoticNestedQuotients AsymptoticRegularTrace ContinuousLinearMap
open scoped lp

variable {G ι : Type*} [Group G] {H : Subgroup G}

theorem projection_diagonal (U : Submodule ℂ ℓ²(Classes H,ℂ)) [CompleteSpace U]
    (q : Classes H) : matrix U.starProjection q q=((‖U.starProjection (delta q)‖^2:ℝ):ℂ) := by
  have hh := gram_diagonal U.starProjection q
  have hsa : U.starProjection.adjoint=U.starProjection := isSelfAdjoint_starProjection U
  have hp : U.starProjection.comp U.starProjection=U.starProjection := U.isIdempotentElem_starProjection
  rwa [hsa,hp] at hh

/-- A subspace contained in every local corner is fixed by the adjoint
of the ordered product, whether or not the local projections commute. -/
theorem projection_comp_word (U : Submodule ℂ ℓ²(Classes H,ℂ)) [CompleteSpace U]
    (V : ι → Submodule ℂ ℓ²(Classes H,ℂ)) [∀ i,CompleteSpace (V i)]
    (l : List ι) (hUV : ∀ i∈l,U≤V i) :
    U.starProjection.comp (word (fun i => (V i).starProjection) l)=U.starProjection := by
  induction l with
  | nil => exact comp_id _
  | cons i l ih =>
    change U.starProjection.comp ((word (fun i => (V i).starProjection) l).comp
      (V i).starProjection)=U.starProjection
    rw [← comp_assoc,ih (fun j hj => hUV j (List.mem_cons_of_mem i hj))]
    exact Submodule.starProjection_comp_starProjection_of_le (hUV i List.mem_cons_self)

/-- The rooted size of any common corner is bounded by the product of
the local rooted sizes. This is the upper bound needed after summing
orthogonal sectors; no sector dimension formula enters. -/
theorem common_corner_diagonal_le (S T : ι → Subgroup G)
    (hS : ∀ i,H≤S i) (hT : ∀ i,H≤T i)
    (hsep : ∀ i,S i⊓T i≤H) (hother : ∀ i j,j≠i → S j≤T i)
    (V : ι → Submodule ℂ ℓ²(Classes H,ℂ)) [∀ i,CompleteSpace (V i)]
    (hV : ∀ i,Supported (hS i) (V i).starProjection)
    (he : ∀ i,Equivariant (V i).starProjection)
    (U : Submodule ℂ ℓ²(Classes H,ℂ)) [CompleteSpace U]
    (l : List ι) (hl : l.Nodup) (hUV : ∀ i∈l,U≤V i) :
    (matrix U.starProjection (classOf H 1) (classOf H 1)).re≤
      (l.map (fun i => (matrix (V i).starProjection (classOf H 1) (classOf H 1)).re)).prod := by
  have hw := word_norm_sq S T hS hT hsep hother (fun i => (V i).starProjection) hV he l hl
  have hn := U.norm_starProjection_apply_le
    (word (fun i => (V i).starProjection) l (delta (classOf H 1)))
  have hp := congrArg (fun B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ) => B (delta (classOf H 1)))
    (projection_comp_word U V l hUV)
  change U.starProjection (word (fun i => (V i).starProjection) l (delta (classOf H 1)))=
    U.starProjection (delta (classOf H 1)) at hp
  rw [hp] at hn
  simp only [projection_diagonal,Complex.ofReal_re]
  rw [← hw]
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

#print axioms projection_diagonal
#print axioms projection_comp_word
#print axioms common_corner_diagonal_le

end AsymptoticQuotientOperators
