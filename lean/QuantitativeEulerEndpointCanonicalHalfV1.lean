module

public import QuantitativeEulerEndpointCornerCutV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCanonicalHalf
open ContinuousLinearMap QuantitativeSpectralCut QuantitativeEulerEndpointSubcorner
open QuantitativeEulerEndpointCornerCut MeasureTheory
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x)
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp

def projection (A : 𝔄) (hA : IsSelfAdjoint A) :
    QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs :=
  (cutElement hact s hs p hp U hU A hA (1/2) (by norm_num)).val

theorem projection_isStarProjection (A : 𝔄) (hA : IsSelfAdjoint A) :
    IsStarProjection (projection hact s hs p hp U hU A hA) :=
  (cutElement_projection hact s hs p hp U hU A hA (1/2) (by norm_num)).map
    (inclusion hact s hs p hp)

def space (A : 𝔄) (x : α) : ClosedSubmodule ℂ ℓ²(G,ℂ) where
  toSubmodule := highAt (ρ A x) (1/2)
  isClosed' := (lowAt (ρ A x) (1/2)).isClosed_orthogonal

theorem projection_representation (A : 𝔄) (hA : IsSelfAdjoint A) (x : α) :
    QuantitativeSpectralRegularAlgebra.representation G α hact s hs
      (projection hact s hs p hp U hU A hA) x=(highAt (ρ A x) (1/2)).starProjection := rfl

theorem space_projection (A : 𝔄) (hA : IsSelfAdjoint A) (x : α) :
    (space hact s hs p hp A x).toSubmodule.starProjection=
      QuantitativeSpectralRegularAlgebra.representation G α hact s hs
        (projection hact s hs p hp U hU A hA) x := rfl

local instance closedSubmodule_complete (V : ClosedSubmodule ℂ ℓ²(G,ℂ)) :
    CompleteSpace V.toSubmodule := V.isClosed.completeSpace_coe

/-- An exact baseline domination is inherited by the canonical hard
source. Monotone soft updates preserve this sufficient condition. -/
theorem space_le_baseline (A : 𝔄) (hA0 : 0≤A)
    (W : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
    (hAW : ∀ x, ρ A x≤(W x).toSubmodule.starProjection) (x : α) :
    (space hact s hs p hp A x).toSubmodule≤(W x).toSubmodule := by
  have hAx0 : 0≤ρ A x := (pointwise_le_iff hact s hs p hp 0 A).mpr hA0 x
  have hW : IsStarProjection (W x).toSubmodule.starProjection :=
    ⟨Submodule.isIdempotentElem_starProjection _,isSelfAdjoint_iff'.mpr (isSelfAdjoint_starProjection _)⟩
  exact highAt_le_corner _ (IsSelfAdjoint.of_nonneg hAx0) (W x).toSubmodule
    (by norm_num) (hW.mul_right_and_mul_left_of_nonneg_of_le hAx0 (hAW x)).1

#print axioms projection_isStarProjection
#print axioms projection_representation
#print axioms space_projection
#print axioms space_le_baseline
end QuantitativeEulerEndpointCanonicalHalf
