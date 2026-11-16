module

public import QuantitativeMaassMajorantTraceNormalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- Exact scalar normalization remains valid after arbitrary bounded
localization of the cylinder columns. -/
theorem originalMajorant_localized_trace_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (t : ℝ)
    (A : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]H) (T : H→L[ℂ]H) :
    columnLinearTrace (quotientMeasure 0)
      (fun z => A (originalMajorantColumn K hc he ε t z)) T =
      (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹^2*
        columnLinearTrace (quotientMeasure 0)
          (fun z => A (enlargedWindowColumn K hc he ε t z)) T := by
  have heq (z : ℍ) : A (originalMajorantColumn K hc he ε t z)=
      ((QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹:ℂ) •
        A (enlargedWindowColumn K hc he ε t z) := by
    rw [originalMajorantColumn_eq_smul,map_smul]
    rfl
  simp_rw [heq]
  simpa only [Complex.ofReal_inv] using columnLinearTrace_column_real_smul (quotientMeasure 0)
    (fun z => A (enlargedWindowColumn K hc he ε t z)) T
    (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹

#print axioms originalMajorant_localized_trace_eq
end QuantitativeMaass.Scheduled
