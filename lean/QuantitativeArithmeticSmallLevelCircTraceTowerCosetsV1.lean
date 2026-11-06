module

public import QuantitativeArithmeticSmallLevelCircTraceDiamondV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.TraceTower

variable {A : Type*} [Group A]
variable (G H K : Subgroup A) (hGH : G ≤ H) (hHK : H ≤ K)

def projection : K ⧸ G.subgroupOf K → K ⧸ H.subgroupOf K :=
  Quotient.map' id (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact hGH hab)

def representative (x : (K ⧸ H.subgroupOf K) × (H ⧸ G.subgroupOf H)) : K :=
  x.1.out * ⟨x.2.out.val, hHK x.2.out.property⟩

def assemble (x : (K ⧸ H.subgroupOf K) × (H ⧸ G.subgroupOf H)) :
    K ⧸ G.subgroupOf K := QuotientGroup.mk (representative G H K hHK x)

theorem projection_assemble (x : (K ⧸ H.subgroupOf K) × (H ⧸ G.subgroupOf H)) :
    projection G H K hGH (assemble G H K hHK x) = x.1 := by
  change QuotientGroup.mk (x.1.out * (⟨x.2.out.val, hHK x.2.out.property⟩ : K)) = x.1
  exact (QuotientGroup.mk_mul_of_mem x.1.out
    (show (⟨x.2.out.val, hHK x.2.out.property⟩ : K) ∈ H.subgroupOf K from
      x.2.out.property)).trans (Quotient.out_eq x.1)

include hGH in
theorem assemble_injective : Function.Injective (assemble G H K hHK) := by
  rintro ⟨a,c⟩ ⟨b,d⟩ he
  have hab := congrArg (projection G H K hGH) he
  rw [projection_assemble, projection_assemble] at hab
  dsimp only [Prod.fst] at hab
  subst b
  have hcd : (QuotientGroup.mk c.out : H ⧸ G.subgroupOf H) = QuotientGroup.mk d.out := by
    apply QuotientGroup.eq.mpr
    rw [assemble, assemble, QuotientGroup.eq] at he
    change (a.out.val*c.out.val)⁻¹*(a.out.val*d.out.val) ∈ G at he
    change c.out.val⁻¹*d.out.val ∈ G
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using he
  change Quotient.mk _ c.out = Quotient.mk _ d.out at hcd
  rw [Quotient.out_eq, Quotient.out_eq] at hcd
  cases hcd
  rfl

/-- Representative-compatible decomposition of relative cosets along a subgroup tower. -/
def equiv [G.IsFiniteRelIndex H] [H.IsFiniteRelIndex K] [G.IsFiniteRelIndex K] :
    (K ⧸ H.subgroupOf K) × (H ⧸ G.subgroupOf H) ≃ K ⧸ G.subgroupOf K := by
  classical
  let := Fintype.ofFinite (K ⧸ H.subgroupOf K)
  let := Fintype.ofFinite (H ⧸ G.subgroupOf H)
  let := Fintype.ofFinite (K ⧸ G.subgroupOf K)
  apply Equiv.ofBijective (assemble G H K hHK)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨assemble_injective G H K hGH hHK, ?_⟩
  have hi := Subgroup.relIndex_mul_relIndex G H K hGH hHK
  change Nat.card (H ⧸ G.subgroupOf H) * Nat.card (K ⧸ H.subgroupOf K) =
    Nat.card (K ⧸ G.subgroupOf K) at hi
  simpa only [Fintype.card_prod, Nat.card_eq_fintype_card, mul_comm] using hi

theorem equiv_apply [G.IsFiniteRelIndex H] [H.IsFiniteRelIndex K] [G.IsFiniteRelIndex K]
    (x : (K ⧸ H.subgroupOf K) × (H ⧸ G.subgroupOf H)) :
    equiv G H K hGH hHK x = QuotientGroup.mk (representative G H K hHK x) := rfl

#print axioms assemble_injective
#print axioms equiv
end QuantitativeArithmeticSmallLevelCirc.TraceTower
