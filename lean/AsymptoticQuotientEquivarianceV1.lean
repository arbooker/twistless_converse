module

public import AsymptoticQuotientSupportV1
public import AsymptoticPolarPermutationInvariantV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticQuotientOperators

open AsymptoticNestedQuotients AsymptoticRegularTrace AsymptoticPermutationInvariant
open scoped lp

variable {G : Type*} [Group G] {H J : Subgroup G}

/-- Right-translation equivariance of a fixed coset-space operator. -/
def Equivariant (B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)) : Prop :=
  ∀ a : G,Invariant (rightMulEquiv H a) B

theorem equivariant_diagonal (B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ))
    (hB : Equivariant B) (q : Classes H) :
    matrix B q q=matrix B (classOf H 1) (classOf H 1) := by
  have hh := hB q.out (classOf H 1) (classOf H 1)
  simpa only [rightMulEquiv_classOf,one_mul,show classOf H q.out=q from q.out_eq] using hh

theorem equivariant_old (h : H≤J) [Finite (J ⧸ H.subgroupOf J)] :
    Equivariant (space h).starProjection := by
  intro a q r
  change (space h).starProjection (delta (rightMulEquiv H a r)) (rightMulEquiv H a q)=
    (space h).starProjection (delta r) q
  rw [projection_matrix,projection_matrix]
  rw [forget_rightMul h a q,forget_rightMul h a r]
  by_cases hqr : forget h q=forget h r
  · rw [ite_eq_left (congrArg (rightMulEquiv J a) hqr),ite_eq_left hqr]
  · rw [ite_eq_right (fun he => hqr ((rightMulEquiv J a).injective he)),ite_eq_right hqr]

theorem equivariant_one : Equivariant (1 : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)) :=
  fun a => invariant_one (rightMulEquiv H a)

theorem equivariant_comp (B C : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ))
    (hB : Equivariant B) (hC : Equivariant C) : Equivariant (B.comp C) :=
  fun a => invariant_comp (rightMulEquiv H a) B C (hB a) (hC a)

theorem equivariant_adjoint (B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ))
    (hB : Equivariant B) : Equivariant B.adjoint :=
  fun a => invariant_adjoint (rightMulEquiv H a) B (hB a)

theorem equivariant_joint_kernel (B C : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ))
    (hB : Equivariant B) (hC : Equivariant C) :
    Equivariant ((B.adjoint.comp B)+(C.adjoint.comp C)).ker.starProjection := by
  intro a
  apply invariant_kernel
  apply invariant_add
  · exact invariant_comp (rightMulEquiv H a) _ _ (invariant_adjoint _ _ (hB a)) (hB a)
  · exact invariant_comp (rightMulEquiv H a) _ _ (invariant_adjoint _ _ (hC a)) (hC a)

#print axioms equivariant_diagonal
#print axioms equivariant_old
#print axioms equivariant_one
#print axioms equivariant_comp
#print axioms equivariant_adjoint
#print axioms equivariant_joint_kernel

end AsymptoticQuotientOperators
