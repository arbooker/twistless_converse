module

public import QuantitativeEulerEndpointSpectralWindowV1
public import QuantitativeEulerEndpointSubcornerV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCornerCut
open ContinuousLinearMap AsymptoticRegularTrace QuantitativeSpectralCut
open QuantitativeSpectralCutRegularity QuantitativeEulerEndpointSubcorner
open QuantitativeEulerEndpointSpectralWindow MeasureTheory
open scoped lp ENNReal CStarAlgebra

section Hilbert
variable {𝔅 H : Type*} [CStarAlgebra 𝔅]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem map_cfc_value (φ : 𝔅 →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (A : 𝔅) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0=0) :
    φ (cfc f A)=AsymptoticFunctionalCalculus.value f (φ A) := by
  have hh := φ.map_cfcₙ f A hf.continuousOn hf0 (map_continuous φ) hA (hA.map φ)
  simpa only [cfcₙ_eq_cfc hf.continuousOn hf0,AsymptoticFunctionalCalculus.value] using hh
end Hilbert

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp

def evaluation (x : α) : 𝔄 →⋆ₙₐ[ℂ] (ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) where
  toFun a := ρ a x
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

theorem representation_cfc (A : 𝔄) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0=0) (x : α) :
    ρ (cfc f A) x=AsymptoticFunctionalCalculus.value f (ρ A x) := by
  exact map_cfc_value (evaluation hact s hs p hp x) A hA f hf hf0

local instance closedSubmodule_complete (V : ClosedSubmodule ℂ ℓ²(G,ℂ)) :
    CompleteSpace V.toSubmodule := V.isClosed.completeSpace_coe

variable (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x)

include U hU in
def cutElement (A : 𝔄) (hA : IsSelfAdjoint A) (a : ℝ) (ha : 0≤a) : 𝔄 := by
  have hsa (x : α) : IsSelfAdjoint (ρ A x) := hA.map (evaluation hact s hs p hp x)
  have hr := highAt_regular (ρ A)
    (QuantitativeSpectralRegularAlgebra.representation_matrix_measurable G α hact s hs A.val)
    (QuantitativeSpectralRegularAlgebra.representation_covariant G α hact s hs A.val)
    hsa ‖A‖ (QuantitativeSpectralRegularAlgebra.representation_norm_le G α hact s hs A.val) a
  have hle (x : α) : highAt (ρ A x) a≤(U x).toSubmodule := by
    apply highAt_le_corner _ (hsa x) _ ha
    rw [hU]
    exact congrArg (fun b : 𝔄 => ρ b x) (mul_one A)
  have hright (x : α) : (highAt (ρ A x) a).starProjection.comp
      (QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x)=
      (highAt (ρ A x) a).starProjection := by
    rw [← hU]
    exact Submodule.starProjection_comp_starProjection_of_le (hle x)
  apply ofFamily hact s hs p hp (fun x => (highAt (ρ A x) a).starProjection) 1
    (fun x => (highAt (ρ A x) a).starProjection_norm_le) hr.1 hr.2 _ hright
  intro x
  rw [← hU]
  exact ContinuousLinearMap.ext (fun v => (U x).toSubmodule.starProjection_eq_self_iff.mpr
    (hle x ((highAt (ρ A x) a).starProjection_apply_mem v)))

@[simp] theorem representation_cutElement (A : 𝔄) (hA : IsSelfAdjoint A) (a : ℝ) (ha : 0≤a) :
    ρ (cutElement hact s hs p hp U hU A hA a ha)=
      fun x => (highAt (ρ A x) a).starProjection := rfl

theorem cutElement_projection (A : 𝔄) (hA : IsSelfAdjoint A) (a : ℝ) (ha : 0≤a) :
    IsStarProjection (cutElement hact s hs p hp U hU A hA a ha) := by
  constructor
  · apply representation_injective hact s hs p hp
    funext x
    exact Submodule.isIdempotentElem_starProjection _
  · apply representation_injective hact s hs p hp
    funext x
    exact isSelfAdjoint_starProjection _

theorem intrinsic_window_sandwich (A : 𝔄) (hA : IsSelfAdjoint A)
    {a b : ℝ} (ha : 0≤a) (hab : a<b) :
    cutElement hact s hs p hp U hU A hA b (ha.trans hab.le)≤cfc (window a b) A ∧
      cfc (window a b) A≤cutElement hact s hs p hp U hU A hA a ha := by
  have he (x : α) := representation_cfc hact s hs p hp A hA (window a b)
    (window_continuous hab) (window_zero ha) x
  constructor
  all_goals
    apply (pointwise_le_iff hact s hs p hp _ _).mp
    intro x
    simp only [representation_cutElement,he]
  · exact (window_sandwich _ (hA.map (evaluation hact s hs p hp x)) hab).1
  · exact (window_sandwich _ (hA.map (evaluation hact s hs p hp x)) hab).2

#print axioms representation_cfc
#print axioms cutElement
#print axioms cutElement_projection
#print axioms intrinsic_window_sandwich
end QuantitativeEulerEndpointCornerCut
