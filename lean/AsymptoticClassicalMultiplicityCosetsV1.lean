module

public import AsymptoticClassicalOldIntersectionIndexV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace AsymptoticClassicalCosets

variable {A : Type*} [Group A]
variable (G H K J : Subgroup A) (hGH : G ≤ H) (hKJ : K ≤ J)

/-- The natural map between the two sides of a subgroup diamond. -/
def diamondMap : K ⧸ G.subgroupOf K → J ⧸ H.subgroupOf J :=
  Quotient.map' (fun a : K => (⟨a.val, hKJ a.property⟩ : J)) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact hGH hab)

@[simp] theorem diamondMap_mk (a : K) :
    diamondMap G H K J hGH hKJ (QuotientGroup.mk a) =
      QuotientGroup.mk (⟨a.val, hKJ a.property⟩ : J) := rfl

/-- The intersection condition makes the map on relative cosets injective. -/
theorem diamondMap_injective (hmeet : H ⊓ K = G) :
    Function.Injective (diamondMap G H K J hGH hKJ) := by
  refine Quotient.ind' fun a => ?_
  refine Quotient.ind' fun b => ?_
  intro he
  rw [diamondMap_mk, diamondMap_mk, QuotientGroup.eq] at he
  apply QuotientGroup.eq.mpr
  change a.val⁻¹ * b.val ∈ G
  rw [← hmeet]
  exact ⟨he, K.mul_mem (K.inv_mem a.property) b.property⟩

/-- Equal finite relative indices turn an intersecting subgroup diamond
 into a representative-compatible bijection of cosets. -/
def diamondEquiv [Finite (K ⧸ G.subgroupOf K)] [Finite (J ⧸ H.subgroupOf J)]
    (hmeet : H ⊓ K = G) (hindex : G.relIndex K = H.relIndex J) :
    K ⧸ G.subgroupOf K ≃ J ⧸ H.subgroupOf J := by
  let := Fintype.ofFinite (K ⧸ G.subgroupOf K)
  let := Fintype.ofFinite (J ⧸ H.subgroupOf J)
  apply Equiv.ofBijective (diamondMap G H K J hGH hKJ)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨diamondMap_injective G H K J hGH hKJ hmeet, ?_⟩
  change Nat.card (K ⧸ G.subgroupOf K) = Nat.card (J ⧸ H.subgroupOf J) at hindex
  simpa only [Nat.card_eq_fintype_card] using hindex

@[simp] theorem diamondEquiv_mk
    [Finite (K ⧸ G.subgroupOf K)] [Finite (J ⧸ H.subgroupOf J)]
    (hmeet : H ⊓ K = G) (hindex : G.relIndex K = H.relIndex J) (a : K) :
    diamondEquiv G H K J hGH hKJ hmeet hindex (QuotientGroup.mk a) =
      QuotientGroup.mk (⟨a.val, hKJ a.property⟩ : J) := rfl

#print axioms diamondMap_injective
#print axioms diamondEquiv
#print axioms diamondEquiv_mk

end AsymptoticClassicalCosets
