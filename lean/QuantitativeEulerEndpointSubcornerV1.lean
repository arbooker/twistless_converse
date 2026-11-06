module

public import QuantitativeSpectralRegularEmbeddingV1
public import QuantitativeSpectralRegularOrderV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSubcorner

open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open MeasureTheory
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)

def Subcorner : Type _ := QuantitativeSpectralCornerAlgebra.cornerSubalgebra p
  hp.isIdempotentElem hp.isSelfAdjoint

instance subcornerCStar : CStarAlgebra (Subcorner hact s hs p hp) :=
  inferInstanceAs (CStarAlgebra (QuantitativeSpectralCornerAlgebra.cornerSubalgebra p
    hp.isIdempotentElem hp.isSelfAdjoint))
instance subcornerOrder : PartialOrder (Subcorner hact s hs p hp) := CStarAlgebra.spectralOrder _
instance subcornerStarOrdered : StarOrderedRing (Subcorner hact s hs p hp) :=
  CStarAlgebra.spectralOrderedRing _

def inclusion : Subcorner hact s hs p hp →⋆ₙₐ[ℂ]
    QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

def representation : Subcorner hact s hs p hp →ₗ[ℝ]
    (α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) where
  toFun a := QuantitativeSpectralRegularAlgebra.representation G α hact s hs a.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem representation_injective : Function.Injective (representation hact s hs p hp) := by
  intro a b h
  exact Subtype.ext (QuantitativeSpectralRegularOrder.representation_injective hact s hs h)

theorem pointwise_le_iff (a b : Subcorner hact s hs p hp) :
    (∀ x, representation hact s hs p hp a x ≤ representation hact s hs p hp b x) ↔ a ≤ b := by
  have hinj : Function.Injective (inclusion hact s hs p hp) := fun _ _ h => Subtype.ext h
  exact (QuantitativeSpectralRegularOrder.pointwise_le_iff hact s hs a.val b.val).trans
    (NonUnitalStarAlgHom.map_le_map_iff (inclusion hact s hs p hp) hinj)

theorem representation_one (x : α) : representation hact s hs p hp 1 x =
    QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x := rfl

local notation "ρ₀" => QuantitativeSpectralRegularAlgebra.representation G α hact s hs

def ofFamily (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : ℝ)
    (hn : ∀ x, ‖B x‖ ≤ C) (hm : ∀ g h, Measurable (fun x => matrix (B x) g h))
    (hc : Covariant B) (hl : ∀ x, (ρ₀ p x).comp (B x) = B x)
    (hr : ∀ x, (B x).comp (ρ₀ p x) = B x) : Subcorner hact s hs p hp := by
  change ∀ x, ρ₀ p x * B x = B x at hl
  change ∀ x, B x * ρ₀ p x = B x at hr
  have hpl (x : α) : corner s x * ρ₀ p x = ρ₀ p x := by
    exact congrArg (fun a => ρ₀ a x) (one_mul p)
  have hpr (x : α) : ρ₀ p x * corner s x = ρ₀ p x :=
    QuantitativeSpectralRegularAlgebra.representation_supported G α hact s hs p x
  let a := QuantitativeSpectralRegularEmbedding.ofFamily hact s hs B C hn hm hc
    (fun x => by
      change corner s x * B x = B x
      calc
        corner s x * B x = corner s x * (ρ₀ p x * B x) := by rw [hl]
        _ = B x := by rw [← mul_assoc, hpl, hl])
    (fun x => by
      change B x * corner s x = B x
      calc
        B x * corner s x = (B x * ρ₀ p x) * corner s x := by rw [hr]
        _ = B x := by rw [mul_assoc, hpr, hr])
  refine ⟨a, (Subsemigroup.mem_corner_iff hp.isIdempotentElem).mpr ⟨?_, ?_⟩⟩
  · apply QuantitativeSpectralRegularOrder.representation_injective hact s hs
    funext x
    exact hl x
  · apply QuantitativeSpectralRegularOrder.representation_injective hact s hs
    funext x
    exact hr x

@[simp] theorem representation_ofFamily
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : ℝ)
    (hn : ∀ x, ‖B x‖ ≤ C) (hm : ∀ g h, Measurable (fun x => matrix (B x) g h))
    (hc : Covariant B) (hl : ∀ x, (ρ₀ p x).comp (B x) = B x)
    (hr : ∀ x, (B x).comp (ρ₀ p x) = B x) :
    representation hact s hs p hp (ofFamily hact s hs p hp B C hn hm hc hl hr) = B := rfl

variable (μ : Measure α) (hf : μ s < ∞)

def rootedTrace : Subcorner hact s hs p hp →L[ℝ] ℝ :=
  QuantitativeSpectralTraceFunctional.traceCLM μ hs hf
    (representation hact s hs p hp)
    (fun a => QuantitativeSpectralRegularAlgebra.representation_matrix_measurable G α hact s hs a.val 1 1)
    (fun a => QuantitativeSpectralRegularAlgebra.representation_norm_le G α hact s hs a.val)
    (fun a => QuantitativeSpectralRegularAlgebra.representation_supported G α hact s hs a.val)

theorem rootedTrace_one : rootedTrace hact s hs p hp μ hf 1 =
    QuantitativeSpectralFiniteCornerTrace.rootedTrace μ hact s hs hf p := rfl

theorem rootedTrace_mono : Monotone (rootedTrace hact s hs p hp μ hf) := by
  intro a b hab
  have hinj : Function.Injective (inclusion hact s hs p hp) := fun _ _ h => Subtype.ext h
  exact QuantitativeSpectralFiniteCornerDistribution.rootedTrace_mono hact s hs μ hf
    ((NonUnitalStarAlgHom.map_le_map_iff (inclusion hact s hs p hp) hinj).mpr hab)

theorem rootedTrace_cyclic
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (a b : Subcorner hact s hs p hp) :
    rootedTrace hact s hs p hp μ hf (a*b) = rootedTrace hact s hs p hp μ hf (b*a) :=
  QuantitativeSpectralFiniteCornerTrace.rootedTrace_cyclic μ hact s hs hf hmp a.val b.val

theorem rootedTrace_star (a : Subcorner hact s hs p hp) :
    rootedTrace hact s hs p hp μ hf (star a) = rootedTrace hact s hs p hp μ hf a :=
  QuantitativeSpectralFiniteCornerTrace.rootedTrace_star μ hact s hs hf a.val

theorem log_lower_bound
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    {n : ℕ} (Q : Fin n → Subcorner hact s hs p hp) (hQ : ∑ i, Q i = 1)
    (hid : ∀ i, Q i*Q i = Q i) {V : Subcorner hact s hs p hp}
    (hV : QuantitativeSpectralBlockTriangular.Below Q V 1)
    (B : Subcorner hact s hs p hp) (hB : IsUnit B) (S : Subcorner hact s hs p hp)
    (hdom : star (B*(1+V))*(B*(1+V)) ≤ S) :
    rootedTrace hact s hs p hp μ hf (CFC.log (star B*B)) ≤
      rootedTrace hact s hs p hp μ hf (CFC.log S) := by
  have hu : IsUnit (B*(1+V)) := hB.mul
    ((show IsNilpotent V from ⟨n+1, QuantitativeSpectralBlockTriangular.pow_eq_zero Q hQ hV⟩).isUnit_one_add)
  have hpos : IsStrictlyPositive (star (B*(1+V))*(B*(1+V))) :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mpr ⟨B*(1+V),hu,rfl⟩
  have ht := rootedTrace_mono hact s hs p hp μ hf (CFC.log_le_log hdom hpos)
  have he := QuantitativeSpectralBlockTriangular.trace_log_block_congruence Q hQ hid hV B hB
    (rootedTrace hact s hs p hp μ hf) (rootedTrace_cyclic hact s hs p hp μ hf hmp)
    (rootedTrace_star hact s hs p hp μ hf) 1
  simp only [one_smul] at he
  rwa [he] at ht

#print axioms ofFamily
#print axioms pointwise_le_iff
#print axioms rootedTrace_one
#print axioms rootedTrace_mono
#print axioms log_lower_bound
end QuantitativeEulerEndpointSubcorner
