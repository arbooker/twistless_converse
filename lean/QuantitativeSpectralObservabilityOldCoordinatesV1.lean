module

public import QuantitativeSpectralObservabilityFundamentalPartitionV1
public import AsymptoticCosetTraceSumsV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open scoped lp

/-- The actual old-space orthogonal projection has precisely the finite
coset-average coordinate row, including its index normalization. -/
theorem oldProjection_coordinate (N : ℕ) (J : Subgroup OrbitGroup)
    (hJ : gamma N≤J) [Finite (J ⧸ (gamma N).subgroupOf J)]
    {I : Type*} [Fintype I] (r : I → J)
    (e : I ≃ (J ⧸ (gamma N).subgroupOf J))
    (he : ∀ i, e i=QuotientGroup.mk (r i))
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ)
    (u : ℓ²(OrbitGroup,ℂ)) (hu : u∈quotientSpace N hε ht x) (g : OrbitGroup) :
    coordinate N ε t x g ((AsymptoticCongruenceOldSpace.space N J hJ hε ht x).starProjection u)=
      ∑ i, (((gamma N).subgroupOf J).index:ℂ)⁻¹ *
        coordinate N ε t x ((r i).val⁻¹*g) u := by
  obtain ⟨f,rfl⟩ := hu
  change coordinate N ε t x g
    ((AsymptoticCongruenceOldSpace.space N J hJ hε ht x).starProjection
      (induction N hε ht x f))=_
  simp only [AsymptoticCongruenceOldSpace.projection_induction,coordinate_induction]
  rw [AsymptoticNestedQuotients.projection_apply]
  change (((gamma N).subgroupOf J).index:ℂ)⁻¹ *
    (∑' q : {q // AsymptoticNestedQuotients.forget hJ q=
      AsymptoticNestedQuotients.classOf J g}, f q.val)=_
  rw [AsymptoticNestedQuotients.fibre_sum_eq_coset_sum hJ r e he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z : ℂ => (((gamma N).subgroupOf J).index:ℂ)⁻¹*z)
    (coordinate_induction N hε ht x f ((r i).val⁻¹*g)).symm

theorem oldProjection_range (N : ℕ) (J : Subgroup OrbitGroup)
    (hJ : gamma N≤J) [Finite (J ⧸ (gamma N).subgroupOf J)]
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ)
    (u : ℓ²(OrbitGroup,ℂ)) :
    (AsymptoticCongruenceOldSpace.space N J hJ hε ht x).starProjection u∈
      quotientSpace N hε ht x :=
  AsymptoticCongruenceOldSpace.space_le_quotient N J hJ hε ht x
    (Submodule.starProjection_apply_mem _ _)

#print axioms oldProjection_coordinate
#print axioms oldProjection_range

end QuantitativeSpectralObservability
