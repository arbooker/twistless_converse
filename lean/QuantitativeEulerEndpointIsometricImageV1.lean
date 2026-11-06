module

public import AsymptoticIsometryRangeV1
public import AsymptoticRegularTraceCyclicV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointIsometricImage

open ContinuousLinearMap AsymptoticRegularTrace MeasureTheory
open scoped InnerProduct lp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restrict an ambient isometry on a closed source subspace. -/
def embedding (U : H →L[ℂ] H) (F : Submodule ℂ H) [CompleteSpace F]
    (hU : ∀ v ∈ F, ‖U v‖ = ‖v‖) : F →ₗᵢ[ℂ] H where
  toLinearMap := U.toLinearMap.comp F.subtype
  norm_map' v := hU v v.property

def imageSpace (U : H →L[ℂ] H) (F : Submodule ℂ H) [CompleteSpace F]
    (hU : ∀ v ∈ F, ‖U v‖ = ‖v‖) : Submodule ℂ H :=
  (embedding U F hU).toLinearMap.range

instance imageSpace_complete (U : H →L[ℂ] H) (F : Submodule ℂ H) [CompleteSpace F]
    (hU : ∀ v ∈ F, ‖U v‖ = ‖v‖) : CompleteSpace (imageSpace U F hU) :=
  AsymptoticIsometryRange.range_complete _

/-- The transported closed-space projection is the literal conjugation. -/
theorem image_projection (U : H →L[ℂ] H) (F : Submodule ℂ H) [CompleteSpace F]
    (hU : ∀ v ∈ F, ‖U v‖ = ‖v‖) :
    (imageSpace U F hU).starProjection = U.comp (F.starProjection.comp U.adjoint) := by
  change (embedding U F hU).toLinearMap.range.starProjection = _
  rw [← AsymptoticIsometryRange.cogram]
  change (U.comp F.subtypeL).comp (U.comp F.subtypeL).adjoint = _
  rw [adjoint_comp, comp_assoc, ← comp_assoc F.subtypeL F.subtypeL.adjoint]
  rw [Submodule.adjoint_subtypeL]
  rfl

/-- Restriction followed by the original ambient isometry has precisely the
source projection as its Gram operator. -/
theorem restricted_gram (U : H →L[ℂ] H) (F : Submodule ℂ H) [CompleteSpace F]
    (hU : ∀ v ∈ F, ‖U v‖ = ‖v‖) :
    (U.comp F.starProjection).adjoint.comp (U.comp F.starProjection) = F.starProjection := by
  let I := (embedding U F hU).toContinuousLinearMap
  have hI : I.adjoint.comp I = 1 := (embedding U F hU).adjoint_comp_self
  have he : U.comp F.starProjection = I.comp F.subtypeL.adjoint := by
    rw [Submodule.adjoint_subtypeL]
    rfl
  rw [he, adjoint_comp, adjoint_adjoint, comp_assoc,
    ← comp_assoc I.adjoint I, hI, one_def, id_comp, Submodule.adjoint_subtypeL]
  rfl

theorem restricted_cogram (U : H →L[ℂ] H) (F : Submodule ℂ H) [CompleteSpace F]
    (hU : ∀ v ∈ F, ‖U v‖ = ‖v‖) :
    (U.comp F.starProjection).comp (U.comp F.starProjection).adjoint =
      (imageSpace U F hU).starProjection := by
  rw [image_projection, adjoint_comp, show F.starProjection.adjoint = F.starProjection from
    isSelfAdjoint_starProjection F, comp_assoc,
    ← comp_assoc F.starProjection F.starProjection,
    show F.starProjection.comp F.starProjection = F.starProjection from
      F.isIdempotentElem_starProjection]

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- Isometric transport preserves regular trace exactly, including infinite
traces. This is a conclusion for the actual image projection. -/
theorem image_trace (μ : Measure α)
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (U : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (F : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ x, CompleteSpace (F x)] (hi : ∀ x v, v ∈ F x → ‖U x v‖ = ‖v‖)
    (hmU : ∀ g h, Measurable (fun x => matrix (U x) g h)) (hcU : Covariant U)
    (hmF : ∀ g h, Measurable (fun x => matrix (F x).starProjection g h))
    (hcF : Covariant (fun x => (F x).starProjection)) :
    trace μ (fun x => (imageSpace (U x) (F x) (hi x)).starProjection) =
      trace μ (fun x => (F x).starProjection) := by
  have ht := trace_adjoint_mul hmp (fun x => (U x).comp (F x).starProjection)
    (matrix_comp_measurable _ _ hmU hmF) (covariant_comp _ _ hcU hcF)
  simpa only [restricted_gram _ _ (hi _), restricted_cogram _ _ (hi _)] using ht.symm

#print axioms image_projection
#print axioms restricted_gram
#print axioms restricted_cogram
#print axioms image_trace

end QuantitativeEulerEndpointIsometricImage
