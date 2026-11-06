module

public import QuantitativeEulerEndpointRegularBaseV1
public import QuantitativeEulerEndpointImageV1
public import QuantitativeSpectralExceptionalRowsV1
public import AsymptoticIntegralBranchSupportV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBandCorner
open UpperHalfPlane MeasureTheory AsymptoticHyperbolicArea AsymptoticOrbitDiagonal
open AsymptoticRegularCompactBranch (Space)
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointRegularBase
open AsymptoticSubgroupSupport
open scoped lp

section Generic
variable {G α : Type*} [Group G] [MulAction G α]
theorem corner_mul_of_subset {s t : Set α} (hst : t⊆s) (x : α) :
    (corner (G:=G) s x)*(corner t x)=corner t x := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext g
  change corner s x (corner t x v) g=corner t x v g
  simp only [corner_apply]
  by_cases ht : g • x∈t
  · simp only [ht,hst ht,ite_true]
  · simp only [ht,ite_false,ite_self]
theorem corner_mul_reverse_of_subset {s t : Set α} (hst : t⊆s) (x : α) :
    (corner (G:=G) t x)*(corner s x)=corner t x := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext g
  change corner t x (corner s x v) g=corner t x v g
  simp only [corner_apply]
  by_cases ht : g • x∈t
  · simp only [ht,hst ht,ite_true]
  · simp only [ht,ite_false]
end Generic

variable {ε : ℝ} (hε : 0<ε) (H : ℝ)
def ambient : Set ℍ := observationRectangle 1 ε H

include hε in
theorem ambient_compact : IsCompact (ambient (ε:=ε) H) := observationRectangle_compact 1 H hε

theorem band_subset : terminal ε\terminal H⊆ambient (ε:=ε) H := by
  intro x hx
  have hre : x.re∈Set.Ico (0:ℝ) 1 := hx.1.1
  have him : x.im≤H := by
    by_contra hh
    exact hx.2 ⟨hx.1.1,lt_of_not_ge hh⟩
  exact ⟨by rw [abs_of_nonneg hre.1]; exact hre.2.le,hx.1.2.le,him⟩

local notation "s₀" => region (ambient (ε:=ε) H)
local notation "hs₀" => region_measurable (ambient_compact hε H)
local notation "band" => region (terminal ε\terminal H)
local notation "𝔠" => Corner (ambient_compact hε H)
local notation "ρ₀" => QuantitativeSpectralRegularAlgebra.representation AsymptoticRationalGroup.Group Base action_measurable s₀ hs₀

def projection : 𝔠 :=
  QuantitativeSpectralRegularEmbedding.ofFamily action_measurable s₀ hs₀
    (corner (G:=AsymptoticRationalGroup.Group) band) 1
    (AsymptoticOrbitRegion.corner_norm_le band)
    (AsymptoticOrbitDiagonal.corner_matrix_measurable action_measurable
      ((terminal_measurable ε).diff (terminal_measurable H)))
    (corner_covariant band)
    (corner_mul_of_subset (band_subset (ε:=ε) H))
    (corner_mul_reverse_of_subset (band_subset (ε:=ε) H))

theorem projection_representation (x : Base) : ρ₀ (projection hε H) x=corner band x := rfl

theorem projection_isStarProjection : IsStarProjection (projection hε H) := by
  constructor
  · apply QuantitativeSpectralRegularOrder.representation_injective action_measurable s₀ hs₀
    funext x
    exact corner_idempotent band x
  · apply QuantitativeSpectralRegularOrder.representation_injective action_measurable s₀ hs₀
    funext x
    exact corner_adjoint band x

def space (x : Base) : ClosedSubmodule ℂ Space where
  toSubmodule := AsymptoticOrbitRegion.Space band x
  isClosed' := (completeSpace_coe_iff_isComplete.mp
    (inferInstance : CompleteSpace (AsymptoticOrbitRegion.Space band x))).isClosed

theorem space_representation (x : Base) : (space (ε:=ε) H x).toSubmodule.starProjection=
    ρ₀ (projection hε H) x := QuantitativeSpectralExceptionalRows.region_projection band x

theorem projection_supported (S : Subgroup AsymptoticRationalGroup.Group) (x : Base) :
    Supported S (ρ₀ (projection hε H) x) := AsymptoticSubgroupSupport.supported_corner S band x

#print axioms band_subset
#print axioms projection_isStarProjection
#print axioms space_representation
#print axioms projection_supported
end QuantitativeEulerEndpointBandCorner
