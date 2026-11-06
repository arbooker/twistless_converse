module

public import QuantitativeEulerOldProjectionTransportV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionBlock

open ContinuousLinearMap InnerProductSpace AsymptoticNestedQuotients
open scoped InnerProduct lp

section Abstract
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- An intertwiner of self-adjoint operators also intertwines their exact
kernel projections, without invertibility or finite-dimensional assumptions. -/
theorem kernel_intertwine (R : E →L[ℂ] F) (B : E →L[ℂ] E) (C : F →L[ℂ] F)
    (hB : IsSelfAdjoint B) (hC : IsSelfAdjoint C) (hR : R.comp B = C.comp R) (v : E) :
    R (B.ker.starProjection v) = C.ker.starProjection (R v) := by
  have he (x : E) : R (B x) = C (R x) := congrArg (fun T : E →L[ℂ] F => T x) hR
  have ha : B.comp R.adjoint = R.adjoint.comp C := by
    have hh := congrArg (fun T : E →L[ℂ] F => T.adjoint) hR
    simpa only [adjoint_comp, hB.adjoint_eq, hC.adjoint_eq] using hh
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change C (R (B.ker.starProjection v)) = 0
    have hz : B (B.ker.starProjection v) = 0 := B.ker.starProjection_apply_mem v
    rw [← he, hz, map_zero]
  · intro w hw
    rw [← map_sub, ← R.adjoint_inner_right]
    apply B.ker.starProjection_inner_eq_zero
    change B (R.adjoint w) = 0
    have hh := congrArg (fun T : F →L[ℂ] E => T w) ha
    change B (R.adjoint w) = R.adjoint (C w) at hh
    rw [hh, show C w = 0 from hw, map_zero]

theorem starProjection_gram (U : Submodule ℂ E) [CompleteSpace U] :
    U.starProjection.adjoint.comp U.starProjection = U.starProjection := by
  have hU := isStarProjection_starProjection (U := U)
  rw [hU.isSelfAdjoint.adjoint_eq]
  exact hU.isIdempotentElem
end Abstract

section Cosets
variable {G : Type*} [Group G] {H J K S : Subgroup G}
    (hHJ : H ≤ J) (hHK : H ≤ K) (hJS : J ≤ S) (hKS : K ≤ S)
    [Finite (J ⧸ H.subgroupOf J)] [Finite (K ⧸ H.subgroupOf K)]
    [Finite ((J.subgroupOf S) ⧸ (H.subgroupOf S).subgroupOf (J.subgroupOf S))]
    [Finite ((K.subgroupOf S) ⧸ (H.subgroupOf S).subgroupOf (K.subgroupOf S))]

include hJS hKS in
/-- The exact new projector, not just its defining old equations,
restricts to the same finite root new projector on every join block. -/
theorem cosetBlock_new (g : G) (v : ℓ²(Classes H,ℂ)) :
    cosetBlock (H := H) (S := S) g
        ((AsymptoticQuotientOperators.newSpace hHJ hHK).starProjection v) =
      (AsymptoticQuotientOperators.newSpace (inside_le (S := S) hHJ)
        (inside_le (S := S) hHK)).starProjection (cosetBlock (H := H) (S := S) g v) := by
  simp only [AsymptoticQuotientOperators.newSpace, starProjection_gram]
  apply kernel_intertwine
  · exact (isStarProjection_starProjection (U := space hHJ)).isSelfAdjoint.add
      (isStarProjection_starProjection (U := space hHK)).isSelfAdjoint
  · exact (isStarProjection_starProjection (U := space (inside_le (S := S) hHJ))).isSelfAdjoint.add
      (isStarProjection_starProjection (U := space (inside_le (S := S) hHK))).isSelfAdjoint
  · apply ContinuousLinearMap.ext
    intro w
    change cosetBlock (H := H) (S := S) g
      ((space hHJ).starProjection w + (space hHK).starProjection w) = _
    rw [map_add, cosetBlock_old hHJ hJS, cosetBlock_old hHK hKS]
    rfl

#print axioms kernel_intertwine
#print axioms cosetBlock_new
end Cosets
end QuantitativeEulerOldProjectionBlock
