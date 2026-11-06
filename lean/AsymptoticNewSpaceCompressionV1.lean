module

public import AsymptoticQuotientNewSpaceV1
public import AsymptoticQuotientCompressionV1
public import AsymptoticCongruenceNewTraceV1
public import AsymptoticOvergroupAverageV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane ContinuousLinearMap AsymptoticCongruenceStrip
open AsymptoticCongruenceQuotient
open scoped lp

variable (N : ℕ) (J K : Subgroup AsymptoticRationalGroup.Group)
variable (hJ : gamma N≤J) (hK : gamma N≤K)
variable [Finite (J ⧸ (gamma N).subgroupOf J)] [Finite (K ⧸ (gamma N).subgroupOf K)]
variable {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)

theorem newSpace_induction_iff (z : ℍ) (f : ℓ²(Classes N,ℂ)) :
    AsymptoticCongruenceQuotient.induction N hε ht z f∈newSpace N J K hJ hK hε ht z ↔
      f∈AsymptoticQuotientOperators.newSpace hJ hK := by
  change ((AsymptoticCongruenceQuotient.induction N hε ht z f∈quotientSpace N hε ht z ∧
    (space N J hJ hε ht z).starProjection (AsymptoticCongruenceQuotient.induction N hε ht z f)=0) ∧
    (space N K hK hε ht z).starProjection (AsymptoticCongruenceQuotient.induction N hε ht z f)=0) ↔ _
  rw [projection_induction,projection_induction,AsymptoticQuotientOperators.newSpace_mem]
  have hz (v : ℓ²(Classes N,ℂ)) :
      AsymptoticCongruenceQuotient.induction N hε ht z v=0 ↔ v=0 := by
    rw [← (AsymptoticCongruenceQuotient.induction N hε ht z).map_zero]
    exact (AsymptoticCongruenceQuotient.induction N hε ht z).injective.eq_iff
  rw [hz,hz]
  exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨⟨f,rfl⟩,h.1⟩,h.2⟩⟩

theorem newSpace_range (z : ℍ) :
    ((AsymptoticCongruenceQuotient.induction N hε ht z).comp
      (AsymptoticQuotientOperators.newSpace hJ hK).subtypeₗᵢ).toLinearMap.range=
        newSpace N J K hJ hK hε ht z := by
  ext v
  constructor
  · rintro ⟨f,rfl⟩
    exact (newSpace_induction_iff N J K hJ hK hε ht z f).mpr f.property
  · intro hv
    have hq : v∈quotientSpace N hε ht z := hv.1.1
    obtain ⟨f,rfl⟩ := hq
    exact ⟨⟨f,(newSpace_induction_iff N J K hJ hK hε ht z f).mp hv⟩,rfl⟩

/-- The exact local new projection is the transport of the fixed coset
kernel projection, so its trace can be combined with the separated
operator-product bound. -/
theorem newSpace_projection_compression (z : ℍ) :
    (newSpace N J K hJ hK hε ht z).starProjection=
      compression N hε ht (AsymptoticQuotientOperators.newSpace hJ hK).starProjection z := by
  have hh := AsymptoticIsometryRange.cogram_comp
    (AsymptoticCongruenceQuotient.induction N hε ht z)
    (AsymptoticQuotientOperators.newSpace hJ hK).subtypeₗᵢ
  have hr : (AsymptoticQuotientOperators.newSpace hJ hK).subtypeₗᵢ.toLinearMap.range=
      AsymptoticQuotientOperators.newSpace hJ hK := Submodule.range_subtype _
  rw [AsymptoticPolarIsometry.starProjection_congr _ _
    (newSpace_range N J K hJ hK hε ht z),
    AsymptoticPolarIsometry.starProjection_congr _ _ hr] at hh
  exact hh

#print axioms newSpace_induction_iff
#print axioms newSpace_range
#print axioms newSpace_projection_compression

end AsymptoticCongruenceOldSpace
