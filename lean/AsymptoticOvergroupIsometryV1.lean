module

public import AsymptoticNestedQuotientsV1
public import AsymptoticFiniteFiberInductionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticNestedQuotients

open scoped lp Classical

variable {G : Type*} [Group G]

theorem classOf_mul (H : Subgroup G) (a : H) (g : G) : classOf H (a.val*g)=classOf H g := by
  symm
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simpa only [mul_inv_cancel_right] using a.property

variable {H J : Subgroup G} (h : H≤J) [Finite (J ⧸ H.subgroupOf J)]

theorem index_pos : 0<(H.subgroupOf J).index :=
  Nat.pos_of_ne_zero (H.subgroupOf J).index_ne_zero_of_finite

/-- Uniform normalized pullback from large-subgroup cosets to
small-subgroup cosets in counting Hilbert space. -/
noncomputable def isometry : ℓ²(Classes J,ℂ) →ₗᵢ[ℂ] ℓ²(Classes H,ℂ) :=
  AsymptoticFiniteFiberInduction.isometry (forget h) (H.subgroupOf J).index
    index_pos (fibre_card h)

theorem isometry_apply (f : ℓ²(Classes J,ℂ)) (q : Classes H) :
    isometry h f q=AsymptoticFiniteFiberInduction.coefficient (H.subgroupOf J).index*f (forget h q) := rfl

/-- The old range is exactly the square-summable functions invariant
under the larger subgroup. Invariance is stated on actual group labels,
so it is independent of chosen coset representatives. -/
theorem isometry_range_iff (v : ℓ²(Classes H,ℂ)) : v∈(isometry h).toLinearMap.range ↔
    ∀ a : J,∀ g : G,v (classOf H (a.val*g))=v (classOf H g) := by
  change v∈(AsymptoticFiniteFiberInduction.isometry (forget h) (H.subgroupOf J).index
    index_pos (fibre_card h)).toLinearMap.range ↔ _
  rw [AsymptoticFiniteFiberInduction.range_iff]
  constructor
  · rintro ⟨f,hf⟩ a g
    rw [hf,hf,forget_classOf,forget_classOf,classOf_mul]
  · intro hv
    have he : ∀ a b,QuotientGroup.rightRel J a b → v (classOf H a)=v (classOf H b) := by
      intro a b hab
      let j : J := ⟨b*a⁻¹,QuotientGroup.rightRel_apply.mp hab⟩
      simpa only [j,inv_mul_cancel_right] using (hv j a).symm
    refine ⟨Quotient.lift (fun g => v (classOf H g)) he,?_⟩
    intro q
    induction q using Quotient.inductionOn with
    | h g => rfl

noncomputable def space : Submodule ℂ ℓ²(Classes H,ℂ) := (isometry h).toLinearMap.range

noncomputable instance space_complete : CompleteSpace (space h) :=
  (isometry h).isometry.isClosedEmbedding.isClosed_range.completeSpace_coe

theorem projection_matrix (q r : Classes H) :
    (space h).starProjection (AsymptoticRegularTrace.delta r) q=
      if forget h q=forget h r then (((H.subgroupOf J).index:ℝ)⁻¹:ℂ) else 0 := by
  have he : (space h).starProjection=AsymptoticFiniteFiberInduction.projection
      (forget h) (H.subgroupOf J).index index_pos (fibre_card h) :=
    (AsymptoticFiberIsometry.operator_cogram (forget h)
      (fun _ => AsymptoticFiniteFiberInduction.coefficient (H.subgroupOf J).index)
      (AsymptoticFiniteFiberInduction.fibre_hasSum (forget h) (H.subgroupOf J).index
        index_pos (fibre_card h))).symm
  rw [he]
  have hm := AsymptoticFiniteFiberInduction.projection_matrix (forget h) (H.subgroupOf J).index
    index_pos (fibre_card h) q r
  by_cases hqr : forget h q=forget h r
  · simpa only [ite_eq_left hqr] using hm
  · simpa only [ite_eq_right hqr] using hm

#print axioms classOf_mul
#print axioms index_pos
#print axioms isometry_apply
#print axioms isometry_range_iff
#print axioms projection_matrix

end AsymptoticNestedQuotients
