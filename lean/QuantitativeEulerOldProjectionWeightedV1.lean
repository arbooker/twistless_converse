module

public import QuantitativeEulerOldProjectionRepeatedV1
public import AsymptoticNewSpaceCompressionV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionBlock

open ContinuousLinearMap AsymptoticNestedQuotients AsymptoticCongruenceStrip UpperHalfPlane
open scoped lp

section Abstract
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem compressed_apply_isometry (U : E →ₗᵢ[ℂ] F) (B : E →L[ℂ] E) (v : E) :
    (U.toContinuousLinearMap.comp B).comp U.toContinuousLinearMap.adjoint (U v) = U (B v) := by
  have he := congrArg (fun T : E →L[ℂ] E => T v) U.adjoint_comp_self
  change U.toContinuousLinearMap.adjoint (U v) = v at he
  change U (B (U.toContinuousLinearMap.adjoint (U v))) = U (B v)
  rw [he]
end Abstract

variable (N : ℕ) (J K S : Subgroup AsymptoticRationalGroup.Group)
    (hJ : gamma N ≤ J) (hK : gamma N ≤ K) (hJS : J ≤ S) (hKS : K ≤ S)
    [Finite (J ⧸ (gamma N).subgroupOf J)] [Finite (K ⧸ (gamma N).subgroupOf K)]
    [((gamma N).subgroupOf S).FiniteIndex]

/-- The literal weighted local new projector intertwines normalized
induction, not merely the equations defining its range. -/
theorem weighted_new_induction {ε : ℝ} (hε : 0 < ε) {t : ℕ} (ht : 1 ≤ t)
    (z : ℍ) (f : ℓ²(AsymptoticCongruenceQuotient.Classes N,ℂ)) :
    (AsymptoticCongruenceOldSpace.newSpace N J K hJ hK hε ht z).starProjection
      (AsymptoticCongruenceQuotient.induction N hε ht z f) =
    AsymptoticCongruenceQuotient.induction N hε ht z
      ((AsymptoticQuotientOperators.newSpace hJ hK).starProjection f) := by
  rw [AsymptoticCongruenceOldSpace.newSpace_projection_compression]
  exact compressed_apply_isometry _ _ f

include hJS hKS in
/-- One positive constant controls the actual weighted regular new corner
for every base point, truncation height and weight. It is obtained from the
finite join and is independent of all the geometric parameters. -/
theorem weighted_old_gap :
    ∃ γ : ℝ, 0 < γ ∧ ∀ {ε : ℝ} (hε : 0 < ε) {t : ℕ} (ht : 1 ≤ t)
      (z : ℍ) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)),
      v ∈ AsymptoticCongruenceQuotient.quotientSpace N hε ht z →
      γ * ‖v - (AsymptoticCongruenceOldSpace.newSpace N J K hJ hK hε ht z).starProjection v‖^2 ≤
        ‖(AsymptoticCongruenceOldSpace.space N J hJ hε ht z).starProjection v‖^2 +
        ‖(AsymptoticCongruenceOldSpace.space N K hK hε ht z).starProjection v‖^2 := by
  obtain ⟨γ, hγ, hg⟩ := ambient_old_gap hJ hK hJS hKS
  refine ⟨γ, hγ, ?_⟩
  intro ε hε t ht z v hv
  obtain ⟨f, rfl⟩ := hv
  simp only [LinearIsometry.coe_toLinearMap]
  rw [weighted_new_induction,
    AsymptoticCongruenceOldSpace.projection_induction,
    AsymptoticCongruenceOldSpace.projection_induction,
    ← map_sub]
  simpa only [LinearIsometry.norm_map] using hg f

#print axioms weighted_new_induction
#print axioms weighted_old_gap
end QuantitativeEulerOldProjectionBlock
