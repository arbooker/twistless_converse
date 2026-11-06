module

public import AsymptoticQuotientRightActionV1
public import AsymptoticPolarPartitionSupportV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticQuotientOperators

open AsymptoticNestedQuotients AsymptoticRegularTrace
open scoped lp

variable {G : Type*} [Group G] {H J K : Subgroup G}

/-- Subgroup support on a coset Hilbert space is preservation of the
partition into cosets of the larger group. -/
def Supported (h : H≤J) (B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)) : Prop :=
  AsymptoticPartitionSupport.Supported (forget h) B

theorem supported_iff (h : H≤J) (B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)) :
    Supported h B ↔ ∀ g k : G,g*k⁻¹∉J → matrix B (classOf H g) (classOf H k)=0 := by
  constructor
  · intro hb g k hgk
    apply hb
    change classOf J g≠classOf J k
    exact fun he => hgk ((classOf_eq_iff J g k).mp he)
  · intro hb q r hqr
    have hq : classOf H q.out=q := q.out_eq
    have hr : classOf H r.out=r := r.out_eq
    rw [← hq,← hr]
    apply hb
    intro hm
    apply hqr
    rw [← hq,← hr,forget_classOf,forget_classOf]
    exact (classOf_eq_iff J q.out r.out).mpr hm

theorem supported_mono (hJ : H≤J) (hK : H≤K) (hJK : J≤K)
    (B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)) (hB : Supported hJ B) : Supported hK B := by
  rw [supported_iff] at hB ⊢
  intro g k hgk
  exact hB g k (fun hj => hgk (hJK hj))

theorem supported_old (h : H≤J) [Finite (J ⧸ H.subgroupOf J)] :
    Supported h (space h).starProjection := by
  intro q r hqr
  change (space h).starProjection (delta r) q=0
  rw [projection_matrix,ite_eq_right hqr]

theorem supported_kernel (h : H≤J) (B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ))
    (hB : Supported h B) : Supported h B.ker.starProjection :=
  AsymptoticPartitionSupport.supported_kernel (forget h) B hB

/-- Exact kernel projections retain local support even when they are
strong limits rather than finite coset sums. -/
theorem supported_joint_kernel (h : H≤J)
    (B C : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ))
    (hB : Supported h B) (hC : Supported h C) :
    Supported h ((B.adjoint.comp B)+(C.adjoint.comp C)).ker.starProjection := by
  apply supported_kernel
  apply AsymptoticPartitionSupport.supported_add
  · exact AsymptoticPartitionSupport.supported_comp (forget h) _ _
      (AsymptoticPartitionSupport.supported_adjoint (forget h) _ hB) hB
  · exact AsymptoticPartitionSupport.supported_comp (forget h) _ _
      (AsymptoticPartitionSupport.supported_adjoint (forget h) _ hC) hC

#print axioms supported_iff
#print axioms supported_mono
#print axioms supported_old
#print axioms supported_kernel
#print axioms supported_joint_kernel

end AsymptoticQuotientOperators
