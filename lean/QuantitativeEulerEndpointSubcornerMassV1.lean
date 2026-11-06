module

public import QuantitativeEulerEndpointSubcornerCheckV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSubcornerMass
open AsymptoticRegularTrace
open QuantitativeSpectralRegularAlgebra QuantitativeSpectralRegularOrder
open QuantitativeSpectralFiniteCornerDistribution QuantitativeSpectralFiniteCornerTrace
open MeasureTheory
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (μ : Measure α) (hf : μ s < ∞)

include hp in
/-- The incoming subcorner mass is the actual regular orbit trace of its
projection, including when p is a survivor of earlier blocks. -/
theorem initial_trace_eq : rootedTrace μ hact s hs hf p =
    (trace μ (representation G α hact s hs p)).toReal := by
  change signedTrace μ (representation G α hact s hs p) = _
  apply signedTrace_eq_toReal μ _ (representation_matrix_measurable G α hact s hs p 1 1)
  intro x
  exact ContinuousLinearMap.nonneg_iff_isPositive.mp
    ((pointwise_le_iff hact s hs 0 p).mpr hp.nonneg x)

include hp in
/-- Every block starts with mass bounded by the original finite region,
so the additive regularization error admits one uniform coefficient. -/
theorem initial_trace_bounds : 0 ≤ rootedTrace μ hact s hs hf p ∧
    rootedTrace μ hact s hs hf p ≤ (μ s).toReal := by
  constructor
  · simpa only [map_zero] using rootedTrace_mono hact s hs μ hf hp.nonneg
  · simpa only [rootedTrace_one hact s hs μ hf] using rootedTrace_mono hact s hs μ hf hp.le_one

variable (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection = representation G α hact s hs p x)
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h))
  (hcB : ∀ i, Covariant (B i)) (C : ℕ → ℝ) (hC : ∀ i x, ‖B i x‖ ≤ C i)
  (c : ℝ) (hc : 0 < c)

include hp hf hU hmB hcB hC hc in
theorem survivor_mass_le_initial (n : ℕ) :
    (trace μ (QuantitativeSpectralRegularPacket.projectionFamily U B c n)).toReal ≤
      (trace μ (representation G α hact s hs p)).toReal := by
  have hproj := QuantitativeEulerEndpointSubcornerDeterminantData.projectionElement_projection
    hact s hs p hp U hU B hmB hcB C hC c hc n
  have h := QuantitativeEulerEndpointSubcorner.rootedTrace_mono hact s hs p hp μ hf hproj.le_one
  rw [QuantitativeEulerEndpointSubcornerSharp.rooted_projection_trace
      hact s hs p hp U hU B hmB hcB C hC c hc μ hf n,
    QuantitativeEulerEndpointSubcorner.rootedTrace_one,
    initial_trace_eq hact s hs p hp μ hf] at h
  exact h

#print axioms initial_trace_eq
#print axioms initial_trace_bounds
#print axioms survivor_mass_le_initial
end QuantitativeEulerEndpointSubcornerMass
