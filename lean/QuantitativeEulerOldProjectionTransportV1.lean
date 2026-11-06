module

public import QuantitativeEulerOldProjectionBlockV1
public import AsymptoticOvergroupAverageV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionBlock

open AsymptoticNestedQuotients ContinuousLinearMap
open scoped lp

variable {G : Type*} [Group G] {H J S : Subgroup G}
    (hHJ : H ≤ J) (hJS : J ≤ S)

include hHJ in
theorem inside_le : H.subgroupOf S ≤ J.subgroupOf S := fun _ h => hHJ h

theorem forget_comp (q : Classes H) :
    forget hJS (forget hHJ q) = forget (hHJ.trans hJS) q := by
  induction q using Quotient.inductionOn with
  | h a => rfl

/-- The translated root chart preserves the actual old-coset partition. -/
theorem forget_translate (g : G) (q : Classes (H.subgroupOf S)) :
    forget hHJ (translateClass (H := H) (J := S) g q) =
      translateClass (H := J) (J := S) g (forget (inside_le (S := S) hHJ) q) := by
  induction q using Quotient.inductionOn with
  | h a => rfl

/-- The entire global old fiber lies in the same join block, and is exactly
one translated copy of the corresponding finite root old fiber. -/
def oldFiberEquiv (g : G) (q : Classes (H.subgroupOf S)) :
    {r : Classes (H.subgroupOf S) //
      forget (inside_le (S := S) hHJ) r = forget (inside_le (S := S) hHJ) q} ≃
    {r : Classes H // forget hHJ r = forget hHJ (translateClass (H := H) (J := S) g q)} :=
  Equiv.ofBijective (fun r => ⟨translateClass g r.val, by
    rw [forget_translate, forget_translate, r.property]⟩) (by
      constructor
      · intro a b hab
        exact Subtype.ext (translateClass_injective g (congrArg Subtype.val hab))
      · intro r
        have ho : forget (hHJ.trans hJS) r.val = classOf S g := by
          rw [← forget_comp hHJ hJS, r.property, forget_comp,
            forget_translateClass (hHJ.trans hJS)]
        obtain ⟨a, ha⟩ := translateClass_surjective_fibre (hHJ.trans hJS) g ⟨r.val, ho⟩
        have he : forget (inside_le (S := S) hHJ) a = forget (inside_le (S := S) hHJ) q := by
          apply translateClass_injective g
          rw [← forget_translate, ← forget_translate, ha]
          exact r.property
        exact ⟨⟨a, he⟩, Subtype.ext ha⟩)

include hJS in
theorem inside_index : ((H.subgroupOf S).subgroupOf (J.subgroupOf S)).index =
    (H.subgroupOf J).index :=
  Subgroup.relIndex_subgroupOf hJS

variable [Finite (J ⧸ H.subgroupOf J)]

include hJS in
theorem inside_finite : Finite ((J.subgroupOf S) ⧸
    (H.subgroupOf S).subgroupOf (J.subgroupOf S)) := by
  let : ((H.subgroupOf S).subgroupOf (J.subgroupOf S)).FiniteIndex := ⟨by
    rw [inside_index hJS]
    exact Subgroup.index_ne_zero_of_finite⟩
  infer_instance

variable [Finite ((J.subgroupOf S) ⧸ (H.subgroupOf S).subgroupOf (J.subgroupOf S))]

include hJS in
/-- Literal old averaging commutes with restriction to every translated
root block. All coefficients, fibers and indices are the actual coset ones. -/
theorem cosetBlock_old (g : G) (v : ℓ²(Classes H,ℂ)) :
    cosetBlock (H := H) (S := S) g ((space hHJ).starProjection v) =
      (space (inside_le (S := S) hHJ)).starProjection
        (cosetBlock (H := H) (S := S) g v) := by
  ext q
  change (space hHJ).starProjection v (translateClass g q) = _
  rw [projection_apply, projection_apply, inside_index hJS]
  congr 1
  exact ((oldFiberEquiv hHJ hJS g q).tsum_eq (fun r => v r.val)).symm

#print axioms cosetBlock_old
#print axioms forget_translate
#print axioms oldFiberEquiv
end QuantitativeEulerOldProjectionBlock
