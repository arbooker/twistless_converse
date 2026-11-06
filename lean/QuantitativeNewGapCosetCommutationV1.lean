module

public import QuantitativeNewGapCosetIntersectionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticNestedQuotients AsymptoticRegularTrace AsymptoticQuotientOperators
open AsymptoticPermutationInvariant
open scoped lp Pointwise

variable {G : Type*} [Group G] {H J K : Subgroup G} (hJ : H≤J) (hK : H≤K)
variable [Finite (J ⧸ H.subgroupOf J)] [Finite (K ⧸ H.subgroupOf K)]

/-- The literal product of finite coset averages counts the actual
intersection of its two averaging fibres. -/
theorem old_projection_product_matrix (q r : Classes H) :
    matrix ((space hJ).starProjection.comp (space hK).starProjection) q r=
      ((H.subgroupOf J).index:ℂ)⁻¹*((H.subgroupOf K).index:ℂ)⁻¹*
        (Nat.card (jointFibre hJ hK q r):ℂ) := by
  classical
  let F := {s : Classes H // forget hJ s=forget hJ q}
  let S := {s : F // forget hK s.val=forget hK r}
  let e : S ≃ jointFibre hJ hK q r :=
    { toFun := fun s => ⟨s.val.val,s.val.property,s.property⟩
      invFun := fun s => ⟨⟨s.val,s.property.1⟩,s.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let c : ℂ := ((H.subgroupOf K).index:ℂ)⁻¹
  have hh : (∑' s : F, if forget hK s.val=forget hK r then c else 0)=
      (Nat.card (jointFibre hJ hK q r):ℂ)*c := by
    have ht := tsum_subtype {s : F | forget hK s.val=forget hK r} (fun _ => c)
    simp only [Set.indicator_apply,Set.mem_ofPred_eq] at ht
    change (∑' s : S,c)=∑' s : F,if forget hK s.val=forget hK r then c else 0 at ht
    rw [← ht,e.tsum_eq (fun _ => c)]
    let : Fintype (jointFibre hJ hK q r) := Fintype.ofFinite _
    rw [tsum_fintype]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  change (space hJ).starProjection ((space hK).starProjection (delta r)) q=_
  rw [projection_apply]
  have hc : (((H.subgroupOf K).index:ℝ)⁻¹:ℂ)=c := by
    dsimp only [c]
    push_cast
    rfl
  simp_rw [projection_matrix]
  simp only [hc]
  rw [hh]
  dsimp only [c]
  ring

/-- Permutable actual overgroups have commuting literal coset-average
projections. The proof uses exact fibre counts, not a commutation premise
about the operators. -/
theorem old_projections_commute
    (hperm : (J : Set G)*(K : Set G)=(K : Set G)*(J : Set G)) :
    Commute (space hJ).starProjection (space hK).starProjection := by
  apply sub_eq_zero.mp
  apply quotient_root_faithful H
  · intro a
    apply invariant_sub
    · exact invariant_comp _ _ _ (equivariant_old hJ a) (equivariant_old hK a)
    · exact invariant_comp _ _ _ (equivariant_old hK a) (equivariant_old hJ a)
  · ext q
    induction q using Quotient.inductionOn with
    | h g =>
      change matrix ((space hJ).starProjection.comp (space hK).starProjection)
        (classOf H g) (classOf H 1)-
        matrix ((space hK).starProjection.comp (space hJ).starProjection)
          (classOf H g) (classOf H 1)=0
      rw [old_projection_product_matrix,old_projection_product_matrix,
        jointFibre_card_commute hJ hK hperm g]
      ring

#print axioms old_projection_product_matrix
#print axioms old_projections_commute

end QuantitativeNewGap
