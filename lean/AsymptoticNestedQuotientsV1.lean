module

public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.Index

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticNestedQuotients

variable {G : Type*} [Group G]

abbrev Classes (H : Subgroup G) := Quotient (QuotientGroup.rightRel H)

def classOf (H : Subgroup G) (g : G) : Classes H := Quotient.mk _ g

/-- Forgetting part of the congruence data, for right cosets. -/
def forget {H J : Subgroup G} (h : H≤J) : Classes H → Classes J :=
  Quotient.map id (fun _ _ hr => QuotientGroup.rightRel_apply.mpr
    (h (QuotientGroup.rightRel_apply.mp hr)))

theorem forget_classOf {H J : Subgroup G} (h : H≤J) (g : G) :
    forget h (classOf H g)=classOf J g := rfl

/-- Decompose the small-subgroup cosets over the large-subgroup cosets.
The second factor has cardinality [J:H]. -/
noncomputable def decomposition {H J : Subgroup G} (h : H≤J) :
    Classes H ≃ Classes J × (J ⧸ H.subgroupOf J) :=
  (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).trans
    ((Subgroup.quotientEquivProdOfLE h).trans
      (Equiv.prodCongr (QuotientGroup.quotientRightRelEquivQuotientLeftRel J).symm (Equiv.refl _)))

theorem decomposition_fst {H J : Subgroup G} (h : H≤J) (q : Classes H) :
    (decomposition h q).1=forget h q := by
  induction q using Quotient.inductionOn with
  | h g =>
    change classOf J (g⁻¹)⁻¹=classOf J g
    rw [inv_inv]

noncomputable def fibreEquiv {H J : Subgroup G} (h : H≤J) (y : Classes J) :
    {q : Classes H // forget h q=y} ≃ (J ⧸ H.subgroupOf J) where
  toFun q := (decomposition h q.val).2
  invFun a := ⟨(decomposition h).symm (y,a),by rw [← decomposition_fst]; simp⟩
  left_inv q := by
    apply Subtype.ext
    apply (decomposition h).injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext ((decomposition_fst h q.val).trans q.property).symm rfl
  right_inv a := by simp

noncomputable instance fibre_finite {H J : Subgroup G} (h : H≤J)
    [Finite (J ⧸ H.subgroupOf J)] (y : Classes J) :
    Finite {q : Classes H // forget h q=y} :=
  Finite.of_equiv (J ⧸ H.subgroupOf J) (fibreEquiv h y).symm

theorem fibre_card {H J : Subgroup G} (h : H≤J) (y : Classes J) :
    Nat.card {q : Classes H // forget h q=y}=(H.subgroupOf J).index :=
  Nat.card_congr (fibreEquiv h y)

#print axioms forget_classOf
#print axioms decomposition_fst
#print axioms fibre_card

end AsymptoticNestedQuotients
