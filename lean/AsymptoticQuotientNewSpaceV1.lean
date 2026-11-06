module

public import AsymptoticJointKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticQuotientOperators

open AsymptoticNestedQuotients AsymptoticRegularTrace
open scoped lp

variable {G : Type*} [Group G] {H J K S : Subgroup G}
variable (hJ : H≤J) (hK : H≤K)
variable [Finite (J ⧸ H.subgroupOf J)] [Finite (K ⧸ H.subgroupOf K)]

/-- The fixed coset-space new corner, as the kernel of the two old
averages. The positive Gram sum supplies its closed-space structure. -/
noncomputable def newSpace : Submodule ℂ ℓ²(Classes H,ℂ) :=
  (((space hJ).starProjection.adjoint.comp (space hJ).starProjection)+
    ((space hK).starProjection.adjoint.comp (space hK).starProjection)).ker

noncomputable instance newSpace_complete : CompleteSpace (newSpace hJ hK) := by
  unfold newSpace
  infer_instance

theorem newSpace_mem (v : ℓ²(Classes H,ℂ)) :
    v∈newSpace hJ hK ↔ (space hJ).starProjection v=0 ∧ (space hK).starProjection v=0 :=
  AsymptoticJointKernel.mem_ker_gram_add _ _ v

theorem newSpace_supported (hS : H≤S) (hJS : J≤S) (hKS : K≤S) :
    Supported hS (newSpace hJ hK).starProjection :=
  supported_joint_kernel hS _ _ (supported_mono hJ hS hJS _ (supported_old hJ))
    (supported_mono hK hS hKS _ (supported_old hK))

theorem newSpace_equivariant : Equivariant (newSpace hJ hK).starProjection :=
  equivariant_joint_kernel _ _ (equivariant_old hJ) (equivariant_old hK)

#print axioms newSpace_mem
#print axioms newSpace_supported
#print axioms newSpace_equivariant

end AsymptoticQuotientOperators
