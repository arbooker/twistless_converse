module

public import QuantitativeNewGapCosetCommutationV1
public import QuantitativeEulerOldProjectionKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticNestedQuotients AsymptoticQuotientOperators AsymptoticPolarIsometry
open QuantitativeEulerOldProjectionBlock
open scoped lp Pointwise

theorem kernelProjections_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (A B : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hc : Commute A B) :
    Commute A.ker.starProjection B.ker.starProjection := by
  have hab : A.comp B.ker.starProjection=B.ker.starProjection.comp A := by
    ext v
    exact kernel_intertwine A B B hB hB hc.eq v
  symm
  ext v
  exact kernel_intertwine B.ker.starProjection A A hA hA hab.symm v

theorem newSpace_eq_old_sum_kernel {G : Type*} [Group G] {H J K : Subgroup G}
    (hJ : H≤J) (hK : H≤K)
    [Finite (J ⧸ H.subgroupOf J)] [Finite (K ⧸ H.subgroupOf K)] :
    newSpace hJ hK=((space hJ).starProjection+(space hK).starProjection).ker := by
  unfold newSpace
  rw [starProjection_gram,starProjection_gram]

/-- Cross-prime arithmetic permutability of the four actual old groups
implies commutation of their exact new projections. -/
theorem new_projections_commute_of_permutable {G : Type*} [Group G]
    {H J K L M : Subgroup G} (hJ : H≤J) (hK : H≤K) (hL : H≤L) (hM : H≤M)
    [Finite (J ⧸ H.subgroupOf J)] [Finite (K ⧸ H.subgroupOf K)]
    [Finite (L ⧸ H.subgroupOf L)] [Finite (M ⧸ H.subgroupOf M)]
    (hJL : (J : Set G)*(L : Set G)=(L : Set G)*(J : Set G))
    (hJM : (J : Set G)*(M : Set G)=(M : Set G)*(J : Set G))
    (hKL : (K : Set G)*(L : Set G)=(L : Set G)*(K : Set G))
    (hKM : (K : Set G)*(M : Set G)=(M : Set G)*(K : Set G)) :
    Commute (newSpace hJ hK).starProjection (newSpace hL hM).starProjection := by
  rw [starProjection_congr _ _ (newSpace_eq_old_sum_kernel hJ hK),
    starProjection_congr _ _ (newSpace_eq_old_sum_kernel hL hM)]
  apply kernelProjections_commute
  · exact (isSelfAdjoint_starProjection _).add (isSelfAdjoint_starProjection _)
  · exact (isSelfAdjoint_starProjection _).add (isSelfAdjoint_starProjection _)
  · exact ((old_projections_commute hJ hL hJL).add_right
      (old_projections_commute hJ hM hJM)).add_left
      ((old_projections_commute hK hL hKL).add_right (old_projections_commute hK hM hKM))

#print axioms kernelProjections_commute
#print axioms new_projections_commute_of_permutable

end QuantitativeNewGap
