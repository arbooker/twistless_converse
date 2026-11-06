module

public import QuantitativeEulerEndpointCornerCutV1
public import QuantitativeEulerEndpointWindowMeasureV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCornerCut
open ContinuousLinearMap AsymptoticRegularTrace QuantitativeSpectralCut
open QuantitativeEulerEndpointSubcorner QuantitativeEulerEndpointSpectralWindow MeasureTheory
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x)
  (μ : Measure α) (hf : μ s<∞)
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp
local notation "τ" => rootedTrace hact s hs p hp μ hf
local notation "hτ" => rootedTrace_mono hact s hs p hp μ hf

/-- The intrinsic cut trace is exactly the original regular orbit trace. -/
theorem cut_trace_eq (A : 𝔄) (hA : IsSelfAdjoint A) (a : ℝ) (ha : 0≤a) :
    τ (cutElement hact s hs p hp U hU A hA a ha)=
      (trace μ (fun x => (highAt (ρ A x) a).starProjection)).toReal := by
  change signedTrace μ (fun x => (highAt (ρ A x) a).starProjection)=_
  apply signedTrace_eq_toReal μ _
  · exact QuantitativeSpectralRegularAlgebra.representation_matrix_measurable G α hact s hs
      (cutElement hact s hs p hp U hU A hA a ha).val 1 1
  · intro x
    apply nonneg_iff_isPositive.mp
    exact (show IsStarProjection ((highAt (ρ A x) a).starProjection) from
      ⟨Submodule.isIdempotentElem_starProjection _,isSelfAdjoint_iff'.mpr (isSelfAdjoint_starProjection _)⟩).nonneg

include U hU in
/-- Actual tracial spectral mass and actual regular high-cut trace bracket
one another at any two separated nonnegative thresholds. No spectral-measure
identification or normality assumption is needed. -/
theorem spectral_mass_high_trace_sandwich (A : 𝔄) (hA : IsSelfAdjoint A)
    {a b : ℝ} (ha : 0≤a) (hab : a<b) :
    (QuantitativeTracialSpectralMeasure.measure τ hτ A hA).real
      {x : spectrum ℝ A | b≤(x:ℝ)}≤
        (trace μ (fun x => (highAt (ρ A x) a).starProjection)).toReal ∧
    (trace μ (fun x => (highAt (ρ A x) b).starProjection)).toReal≤
      (QuantitativeTracialSpectralMeasure.measure τ hτ A hA).real
        {x : spectrum ℝ A | a<(x:ℝ)} := by
  have hw := intrinsic_window_sandwich hact s hs p hp U hU A hA ha hab
  have hm := window_trace_bounds τ hτ A hA hab
  have hlo := hm.1.trans (hτ hw.2)
  have hhi := (hτ hw.1).trans hm.2
  rw [cut_trace_eq hact s hs p hp U hU μ hf A hA a ha] at hlo
  rw [cut_trace_eq hact s hs p hp U hU μ hf A hA b (ha.trans hab.le)] at hhi
  exact ⟨hlo,hhi⟩

#print axioms cut_trace_eq
#print axioms spectral_mass_high_trace_sandwich
end QuantitativeEulerEndpointCornerCut
