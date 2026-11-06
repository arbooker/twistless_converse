module

public import QuantitativeEulerEndpointSpectralWindowV1
public import QuantitativeTracialSpectralMeasureV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSpectralWindow
open MeasureTheory

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- The trace of the explicit continuous window is between the actual
high spectral masses at its endpoints. -/
theorem window_trace_bounds (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA : IsSelfAdjoint A) {a b : ℝ} (hab : a<b) :
    (QuantitativeTracialSpectralMeasure.measure τ hτ A hA).real
      {x : spectrum ℝ A | b≤(x:ℝ)}≤τ (cfc (window a b) A) ∧
    τ (cfc (window a b) A)≤
      (QuantitativeTracialSpectralMeasure.measure τ hτ A hA).real
        {x : spectrum ℝ A | a<(x:ℝ)} := by
  let μ := QuantitativeTracialSpectralMeasure.measure τ hτ A hA
  let E := {x : spectrum ℝ A | b≤(x:ℝ)}
  let F := {x : spectrum ℝ A | a<(x:ℝ)}
  have hE : MeasurableSet E := measurableSet_le measurable_const measurable_subtype_coe
  have hF : MeasurableSet F := measurableSet_lt measurable_const measurable_subtype_coe
  have hiE : Integrable (E.indicator (fun _ => (1:ℝ))) μ := (integrable_const 1).indicator hE
  have hiF : Integrable (F.indicator (fun _ => (1:ℝ))) μ := (integrable_const 1).indicator hF
  have hc : Continuous (fun x : spectrum ℝ A => window a b (x:ℝ)) :=
    (window_continuous hab).comp continuous_subtype_val
  have hi : Integrable (fun x : spectrum ℝ A => window a b (x:ℝ)) μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlow := integral_mono hiE hi (fun x => by
    by_cases hx : x∈E
    · rw [Set.indicator_of_mem hx,window_one hab hx]
    · rw [Set.indicator_of_notMem hx]
      exact window_nonneg hab x)
  have hupp := integral_mono hi hiF (fun x => by
    by_cases hx : x∈F
    · rw [Set.indicator_of_mem hx]
      exact window_le_one hab x
    · rw [Set.indicator_of_notMem hx,window_zero (le_of_not_gt hx)])
  rw [integral_indicator_const 1 hE,smul_eq_mul,mul_one,
    QuantitativeTracialSpectralMeasure.integral_cfc τ hτ A hA (window a b)
      (window_continuous hab).continuousOn] at hlow
  rw [integral_indicator_const 1 hF,smul_eq_mul,mul_one,
    QuantitativeTracialSpectralMeasure.integral_cfc τ hτ A hA (window a b)
      (window_continuous hab).continuousOn] at hupp
  exact ⟨hlow,hupp⟩

#print axioms window_trace_bounds
end QuantitativeEulerEndpointSpectralWindow
