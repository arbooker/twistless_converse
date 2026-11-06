module

public import QuantitativeEulerEndpointCornerCutV1
public import AsymptoticSubgroupSupportV1
public import Mathlib.Algebra.Algebra.Subalgebra.Tower

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSupportAlgebra
open QuantitativeEulerEndpointSubcorner AsymptoticSubgroupSupport
open MeasureTheory Polynomial
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (S : Subgroup G)
  (hP : ∀ x, Supported S (QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x))
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp

/-- Subgroup support is an algebra condition in the actual subcorner.
Its constant1 is the ambient projection p, whose support is explicit. -/
def algebra : StarSubalgebra ℂ 𝔄 where
  carrier := {A | ∀ x, Supported S (ρ A x)}
  zero_mem' := by intro x g h _; rfl
  one_mem' := hP
  add_mem' hA hB := fun x => supported_add S _ _ (hA x) (hB x)
  mul_mem' hA hB := fun x => supported_comp S _ _ (hA x) (hB x)
  algebraMap_mem' c := by
    intro x
    rw [Algebra.algebraMap_eq_smul_one]
    exact supported_smul S _ (hP x) c
  star_mem' hA := fun x => supported_adjoint S _ (hA x)

include hP in
/-- Every real polynomial in a supported source remains supported,
including polynomials with nonzero constant coefficient. -/
theorem polynomial_supported (A : 𝔄) (hA : ∀ x, Supported S (ρ A x)) (z : ℝ[X]) :
    ∀ x, Supported S (ρ (aeval A z) x) := by
  let T : Subalgebra ℝ 𝔄 := (algebra hact s hs p hp S hP).toSubalgebra.restrictScalars ℝ
  have ha : A∈T := hA
  have hh := (aeval (⟨A,ha⟩ : T) z).property
  rw [coe_aeval_mk_apply] at hh
  exact hh

#print axioms algebra
#print axioms polynomial_supported
end QuantitativeEulerEndpointSupportAlgebra
