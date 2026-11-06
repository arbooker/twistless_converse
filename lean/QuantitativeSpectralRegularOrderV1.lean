module

public import QuantitativeSpectralFiniteCornerDistributionV1
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralRegularOrder

open QuantitativeSpectralRegularAlgebra QuantitativeSpectralFiniteCornerDistribution
open MeasureTheory
open scoped lp

section Pointwise

variable {A β : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace β] [DiscreteTopology β]

local instance familyOrder : PartialOrder (BoundedContinuousFunction β A) :=
  PartialOrder.lift (fun f => (f : β → A))
    (fun _ _ h => BoundedContinuousFunction.ext (congrFun h))

/-- Pointwise order is the C*-order on uniformly bounded operator families.
The square root witness is an actual uniformly bounded family. -/
local instance familyStarOrdered : StarOrderedRing (BoundedContinuousFunction β A) := by
  apply StarOrderedRing.of_le_iff
  intro f g
  constructor
  · intro h
    have hp (x : β) : 0 ≤ g x - f x := sub_nonneg.mpr (h x)
    let q : BoundedContinuousFunction β A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun x => CFC.sqrt (g x - f x)) (Real.sqrt (‖g‖ + ‖f‖)) (fun x => by
        rw [CFC.norm_sqrt _ (hp x)]
        exact Real.sqrt_le_sqrt ((norm_sub_le _ _).trans
          (add_le_add (g.norm_coe_le_norm x) (f.norm_coe_le_norm x))))
    refine ⟨q, ?_⟩
    apply BoundedContinuousFunction.ext
    intro x
    change g x = f x + star (CFC.sqrt (g x - f x)) * CFC.sqrt (g x - f x)
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq, CFC.sqrt_mul_sqrt_self _ (hp x)]
    abel
  · rintro ⟨q,rfl⟩
    intro x
    exact le_add_of_nonneg_right (star_mul_self_nonneg (q x))

end Pointwise

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]

attribute [local instance] familyOrder familyStarOrdered

variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)

/-- The faithful nonunital star representation into all bounded families.
Its unit maps to the terminal region projection. -/
def inclusion : FiniteCorner G α hact s hs →⋆ₙₐ[ℂ] BoundedFamily G α where
  toFun a := a.val.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

theorem inclusion_injective : Function.Injective (inclusion hact s hs) := by
  intro a b h
  apply Subtype.ext
  exact Subtype.ext h

theorem representation_injective : Function.Injective (representation G α hact s hs) := by
  intro a b h
  apply inclusion_injective hact s hs
  apply BoundedContinuousFunction.ext
  exact congrFun h

/-- Pointwise Gram inequalities therefore imply the intrinsic order
inequality needed by the concrete rooted trace-log theorem. -/
theorem pointwise_le_iff (a b : FiniteCorner G α hact s hs) :
    (∀ x, representation G α hact s hs a x ≤ representation G α hact s hs b x) ↔ a ≤ b := by
  exact NonUnitalStarAlgHom.map_le_map_iff (inclusion hact s hs) (inclusion_injective hact s hs)

theorem representation_one (x : α) : representation G α hact s hs 1 x =
    AsymptoticOrbitDiagonal.corner s x := rfl

#print axioms inclusion_injective
#print axioms representation_injective
#print axioms pointwise_le_iff
#print axioms representation_one

end QuantitativeSpectralRegularOrder
