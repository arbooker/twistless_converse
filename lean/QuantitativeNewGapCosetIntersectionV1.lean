module

public import QuantitativeNewGapTreeFaithfulV1
public import AsymptoticOvergroupAverageV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticNestedQuotients AsymptoticRegularTrace AsymptoticQuotientOperators
open scoped lp Pointwise

variable {G : Type*} [Group G] {H J K : Subgroup G} (hJ : H≤J) (hK : H≤K)

def jointFibre (q r : Classes H) :=
  {s : Classes H // forget hJ s=forget hJ q ∧ forget hK s=forget hK r}

instance jointFibre_finite [Finite (J ⧸ H.subgroupOf J)] (q r : Classes H) :
    Finite (jointFibre hJ hK q r) :=
  Finite.of_injective (fun s : jointFibre hJ hK q r =>
    (⟨s.val,s.property.1⟩ : {s : Classes H // forget hJ s=forget hJ q}))
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun s : {s : Classes H // forget hJ s=forget hJ q} => s.val) h)

theorem forget_inf_eq_iff (q r : Classes H) :
    forget (show H≤J⊓K from le_inf hJ hK) q=forget (le_inf hJ hK) r ↔
      forget hJ q=forget hJ r ∧ forget hK q=forget hK r := by
  induction q using Quotient.inductionOn with
  | h g =>
    induction r using Quotient.inductionOn with
    | h k =>
      change (classOf (J⊓K) g=classOf (J⊓K) k) ↔
        classOf J g=classOf J k ∧ classOf K g=classOf K k
      rw [classOf_eq_iff,classOf_eq_iff,classOf_eq_iff]
      rfl

theorem jointFibre_card (q r : Classes H) (t : jointFibre hJ hK q r) :
    Nat.card (jointFibre hJ hK q r)=(H.subgroupOf (J⊓K)).index := by
  let e : jointFibre hJ hK q r ≃
      {s : Classes H // forget (le_inf hJ hK) s=forget (le_inf hJ hK) t.val} :=
    { toFun := fun s => ⟨s.val,(forget_inf_eq_iff hJ hK s.val t.val).mpr
        ⟨s.property.1.trans t.property.1.symm,s.property.2.trans t.property.2.symm⟩⟩
      invFun := fun s => ⟨s.val,by
        obtain ⟨h₁,h₂⟩ := (forget_inf_eq_iff hJ hK s.val t.val).mp s.property
        exact ⟨h₁.trans t.property.1,h₂.trans t.property.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (fibre_card (le_inf hJ hK) _)

theorem jointFibre_root_nonempty (g : G) :
    Nonempty (jointFibre hJ hK (classOf H g) (classOf H 1)) ↔
      g∈(J : Set G)*(K : Set G) := by
  constructor
  · rintro ⟨s⟩
    have he : classOf H s.val.out=s.val := s.val.out_eq
    have h₁ : classOf J s.val.out=classOf J g := (congrArg (forget hJ) he).trans s.property.1
    have h₂ : classOf K s.val.out=classOf K 1 := (congrArg (forget hK) he).trans s.property.2
    have hJmem := (classOf_eq_iff J s.val.out g).mp h₁
    have hKmem : s.val.out∈K := by simpa only [inv_one,mul_one] using (classOf_eq_iff K s.val.out 1).mp h₂
    exact ⟨(s.val.out*g⁻¹)⁻¹,J.inv_mem hJmem,s.val.out,hKmem,by group⟩
  · rintro ⟨j,hj,k,hk,rfl⟩
    refine ⟨⟨classOf H k,?_,?_⟩⟩
    · exact (classOf_mul J ⟨j,hj⟩ k).symm
    · change classOf K k=classOf K 1
      rw [classOf_eq_iff,inv_one,mul_one]
      exact hk

/-- Permutability makes the two actual finite fibre intersections
equinumerous, including their empty cases. -/
theorem jointFibre_card_commute (hperm : (J : Set G)*(K : Set G)=(K : Set G)*(J : Set G))
    (g : G) :
    Nat.card (jointFibre hJ hK (classOf H g) (classOf H 1))=
      Nat.card (jointFibre hK hJ (classOf H g) (classOf H 1)) := by
  classical
  by_cases hg : g∈(J : Set G)*(K : Set G)
  · obtain ⟨s⟩ := (jointFibre_root_nonempty hJ hK g).mpr hg
    obtain ⟨t⟩ := (jointFibre_root_nonempty hK hJ g).mpr (hperm ▸ hg)
    rw [jointFibre_card hJ hK _ _ s,jointFibre_card hK hJ _ _ t,inf_comm]
  · have hs : IsEmpty (jointFibre hJ hK (classOf H g) (classOf H 1)) :=
      ⟨fun s => hg ((jointFibre_root_nonempty hJ hK g).mp ⟨s⟩)⟩
    have ht : IsEmpty (jointFibre hK hJ (classOf H g) (classOf H 1)) :=
      ⟨fun s => hg (hperm.symm ▸ (jointFibre_root_nonempty hK hJ g).mp ⟨s⟩)⟩
    simp

#print axioms jointFibre_card
#print axioms jointFibre_root_nonempty
#print axioms jointFibre_card_commute

end QuantitativeNewGap
