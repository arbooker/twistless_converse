module

public import QuantitativeSpectralRegularAlgebraV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
@[expose] public section

open MeasureTheory ContinuousLinearMap
open scoped lp

namespace QuantitativeSpectralRegularEmbedding

open AsymptoticRegularTrace AsymptoticOrbitDiagonal QuantitativeSpectralRegularAlgebra

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
  (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)

/-- Every actual uniformly bounded measurable covariant two-sided supported
family belongs to the concrete corner; no abstract representability hypothesis
is required to use its C*-functional calculus. -/
noncomputable def ofFamily (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : ℝ)
    (hn : ∀ x, ‖B x‖ ≤ C) (hm : ∀ g h, Measurable (fun x => matrix (B x) g h))
    (hc : Covariant B) (hl : ∀ x, (corner s x).comp (B x) = B x)
    (hr : ∀ x, (B x).comp (corner s x) = B x) : FiniteCorner G α hact s hs := by
  let F : BoundedFamily G α :=
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete B C hn
  let R : regularSubalgebra G α := ⟨F,hm,hc⟩
  refine ⟨R, (Subsemigroup.mem_corner_iff
    (regionProjection_idempotent G α hact s hs)).mpr ⟨?_, ?_⟩⟩
  · apply Subtype.ext
    apply BoundedContinuousFunction.ext
    exact hl
  · apply Subtype.ext
    apply BoundedContinuousFunction.ext
    exact hr

@[simp] theorem representation_ofFamily
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : ℝ)
    (hn : ∀ x, ‖B x‖ ≤ C) (hm : ∀ g h, Measurable (fun x => matrix (B x) g h))
    (hc : Covariant B) (hl : ∀ x, (corner s x).comp (B x) = B x)
    (hr : ∀ x, (B x).comp (corner s x) = B x) :
    representation G α hact s hs (ofFamily hact s hs B C hn hm hc hl hr) = B := rfl

theorem norm_ofFamily_le
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (hn : ∀ x, ‖B x‖ ≤ C) (hm : ∀ g h, Measurable (fun x => matrix (B x) g h))
    (hc : Covariant B) (hl : ∀ x, (corner s x).comp (B x) = B x)
    (hr : ∀ x, (B x).comp (corner s x) = B x) :
    ‖ofFamily hact s hs B C hn hm hc hl hr‖ ≤ C :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    continuous_of_discreteTopology hC hn

#print axioms ofFamily
#print axioms representation_ofFamily
#print axioms norm_ofFamily_le

end QuantitativeSpectralRegularEmbedding
