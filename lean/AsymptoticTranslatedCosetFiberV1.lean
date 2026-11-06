module

public import AsymptoticNestedQuotientsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticNestedQuotients

variable {G : Type*} [Group G]
variable {H J : Subgroup G} (h : H≤J)

/-- Transport a relative right coset to the fibre over J*g. -/
def translateClass (g : G) : Classes (H.subgroupOf J) → Classes H :=
  Quotient.map (fun a : J => a.val*g) (by
    intro a b hab
    apply QuotientGroup.rightRel_apply.mpr
    have he := QuotientGroup.rightRel_apply.mp hab
    change b.val*a.val⁻¹∈H at he
    simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left] using he)

theorem translateClass_apply (g : G) (a : J) :
    translateClass g (classOf (H.subgroupOf J) a)=classOf H (a.val*g) := rfl

theorem forget_translateClass (g : G) (q : Classes (H.subgroupOf J)) :
    forget h (translateClass g q)=classOf J g := by
  induction q using Quotient.inductionOn with
  | h a =>
    change classOf J (a.val*g)=classOf J g
    symm
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_inv_cancel_right] using a.property

theorem translateClass_injective (g : G) : Function.Injective (translateClass (H:=H) (J:=J) g) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      have he := QuotientGroup.rightRel_apply.mp (Quotient.exact hab)
      change b.val*a.val⁻¹∈H
      simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left] using he

theorem translateClass_surjective_fibre (g : G)
    (q : {q : Classes H // forget h q=classOf J g}) :
    ∃ a : Classes (H.subgroupOf J),translateClass g a=q.val := by
  obtain ⟨q,hq⟩ := q
  induction q using Quotient.inductionOn with
  | h x =>
    have hx : x*g⁻¹∈J := QuotientGroup.rightRel_apply.mp (Quotient.exact hq.symm)
    refine ⟨classOf (H.subgroupOf J) ⟨x*g⁻¹,hx⟩,?_⟩
    change classOf H (x*g⁻¹*g)=classOf H x
    rw [inv_mul_cancel_right]

noncomputable def translatedFibreEquiv (g : G) :
    Classes (H.subgroupOf J) ≃ {q : Classes H // forget h q=classOf J g} :=
  Equiv.ofBijective (fun a => ⟨translateClass g a,forget_translateClass h g a⟩) (by
    constructor
    · intro a b hab
      exact translateClass_injective g (congrArg Subtype.val hab)
    · intro q
      obtain ⟨a,ha⟩ := translateClass_surjective_fibre h g q
      exact ⟨a,Subtype.ext ha⟩)

/-- Left quotient representatives act by their inverses on the right
coset fibre. This fixes the convention needed for finite trace sums. -/
noncomputable def leftTranslatedFibreEquiv (g : G) :
    (J ⧸ H.subgroupOf J) ≃ {q : Classes H // forget h q=classOf J g} :=
  (QuotientGroup.quotientRightRelEquivQuotientLeftRel (H.subgroupOf J)).symm.trans
    (translatedFibreEquiv h g)

theorem leftTranslatedFibreEquiv_mk (g : G) (a : J) :
    (leftTranslatedFibreEquiv h g (QuotientGroup.mk a)).val=classOf H (a.val⁻¹*g) := rfl

#print axioms translateClass_apply
#print axioms forget_translateClass
#print axioms translateClass_injective
#print axioms translateClass_surjective_fibre
#print axioms leftTranslatedFibreEquiv_mk

end AsymptoticNestedQuotients
