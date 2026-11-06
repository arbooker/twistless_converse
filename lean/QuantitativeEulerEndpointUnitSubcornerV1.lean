module

public import QuantitativeEulerEndpointSubcornerV1
public import QuantitativeEulerEndpointCornerPolynomialV1
public import QuantitativeEulerEndpointSoftUpdateV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointUnitSubcorner
open QuantitativeEulerEndpointSubcorner MeasureTheory Polynomial
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
local notation "𝔄" => QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs

theorem unitProjection : IsStarProjection (1 : 𝔄) := ⟨by simp [IsIdempotentElem],by simp [IsSelfAdjoint]⟩
abbrev UnitCorner := Subcorner hact s hs (1 : 𝔄) (unitProjection hact s hs)

def lift (A : 𝔄) : UnitCorner hact s hs :=
  ⟨A,(Subsemigroup.mem_corner_iff (unitProjection hact s hs).isIdempotentElem).mpr ⟨one_mul A,mul_one A⟩⟩

def value : UnitCorner hact s hs →ₗ[ℝ] 𝔄 where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem value_lift (A : 𝔄) : value hact s hs (lift hact s hs A)=A := rfl
@[simp] theorem value_one : value hact s hs 1=1 := rfl

theorem value_le_iff (A B : UnitCorner hact s hs) :
    value hact s hs A≤value hact s hs B ↔ A≤B :=
  (QuantitativeSpectralRegularOrder.pointwise_le_iff hact s hs _ _).symm.trans
    (pointwise_le_iff hact s hs 1 (unitProjection hact s hs) A B)

theorem lift_nonneg (A : 𝔄) (hA : 0≤A) : 0≤lift hact s hs A :=
  (value_le_iff hact s hs 0 (lift hact s hs A)).mp hA

theorem lift_le_one (A : 𝔄) (hA : A≤1) : lift hact s hs A≤1 :=
  (value_le_iff hact s hs (lift hact s hs A) 1).mp hA

theorem value_aeval (A : UnitCorner hact s hs) (z : ℝ[X]) :
    value hact s hs (aeval A z)=aeval (value hact s hs A) z := by
  simpa only [value_one,mul_one] using
    QuantitativeEulerEndpointCornerPolynomial.map_aeval_corner
      (value hact s hs) (fun _ _ => rfl) A z

theorem value_update (A B : UnitCorner hact s hs) (L : ℕ) :
    value hact s hs (QuantitativeEulerEndpointSoftUpdate.update A B L)=
      QuantitativeEulerEndpointSoftUpdate.update (value hact s hs A) (value hact s hs B) L := by
  have hm (a b : UnitCorner hact s hs) : value hact s hs (a*b)=value hact s hs a*value hact s hs b := rfl
  have hpow (a : UnitCorner hact s hs) (n : ℕ) : value hact s hs (a^n)=(value hact s hs a)^n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ,hm,ih,pow_succ]
  simp only [QuantitativeEulerEndpointSoftUpdate.update,map_sub,hm,hpow,value_one]

theorem trace_value (μ : Measure α) (hf : μ s<∞) (A : UnitCorner hact s hs) :
    rootedTrace hact s hs 1 (unitProjection hact s hs) μ hf A=
      QuantitativeSpectralFiniteCornerTrace.rootedTrace μ hact s hs hf (value hact s hs A) := rfl

#print axioms lift_nonneg
#print axioms lift_le_one
#print axioms value_aeval
#print axioms value_update
#print axioms trace_value
end QuantitativeEulerEndpointUnitSubcorner
