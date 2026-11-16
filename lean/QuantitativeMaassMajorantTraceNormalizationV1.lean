module

public import QuantitativeMaassMajorantRectangleMassV1
public import QuantitativeMaassColumnLinearTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- A real scalar on actual columns scales the quadratic trace by its square. -/
theorem columnLinearTrace_column_real_smul
    {α H : Type*} [MeasurableSpace α] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure α) (c : α→H) (T : H→L[ℂ]H) (r : ℝ) :
    columnLinearTrace μ (fun x => (r:ℂ) • c x) T = r^2*columnLinearTrace μ c T := by
  unfold columnLinearTrace
  have heq (x : α) : (inner ℂ (T ((r:ℂ) • c x)) ((r:ℂ) • c x)).re =
      r^2*(inner ℂ (T (c x)) (c x)).re := by
    rw [map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  simp_rw [heq]
  exact integral_const_mul _ _

namespace Scheduled
/-- The majorant and enlarged unnormalized traces are related through
literal columns and bounded transfer maps, not a spectral pointwise surrogate. -/
theorem originalMajorant_transferred_trace_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (t : ℝ)
    (A : AutomorphicSpace 0→L[ℂ]H) (T : H→L[ℂ]H) :
    columnLinearTrace (quotientMeasure 0)
      (fun z => A (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))) T =
      (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹^2*
        columnLinearTrace (quotientMeasure 0)
          (fun z => A (cylinderAutomorphic (enlargedWindowColumn K hc he ε t z))) T := by
  have heq (z : ℍ) : A (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))=
      ((QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹:ℂ) •
        A (cylinderAutomorphic (enlargedWindowColumn K hc he ε t z)) := by
    rw [originalMajorantColumn_eq_smul,map_smul,map_smul]
    rfl
  simp_rw [heq]
  simpa only [Complex.ofReal_inv] using columnLinearTrace_column_real_smul (quotientMeasure 0)
    (fun z => A (cylinderAutomorphic (enlargedWindowColumn K hc he ε t z))) T
    (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹

/-- The squared normalization tends to one. -/
theorem originalMajorant_normalization_sq_limit (K : SchwartzMap ℝ ℝ)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹^2)
      atTop (𝓝 1) := by
  simpa only [inv_one,one_pow] using
    ((QuantitativeNinaMaass.windowEnergyDenominator_tendsto K ε hε hp).inv₀ one_ne_zero).pow 2

#print axioms originalMajorant_transferred_trace_eq
#print axioms originalMajorant_normalization_sq_limit
end Scheduled
#print axioms columnLinearTrace_column_real_smul
end QuantitativeMaass
