module

public import QuantitativeEulerEndpointSpectralWindowV1
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSpectralWindow
open Polynomial
variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- Two fixed continuous windows approximate the half-threshold projection
in trace at a cost controlled by the actual idempotency defect. -/
theorem window_defect_bounds (A : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) :
    A-(4:ℝ) • (A-A^2)≤cfc (window (1/2) (3/4)) A ∧
      cfc (window (1/4) (1/2)) A≤A+(4:ℝ) • (A-A^2) := by
  have hA := IsSelfAdjoint.of_nonneg hA0
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg A hA0).mpr hA1
  have hb (x : ℝ) (hx : x∈spectrum ℝ A) : 0≤x ∧ x≤1 := by
    exact ⟨spectrum_nonneg_of_nonneg hA0 hx,(le_abs_self x).trans
      ((quasispectrum.norm_le_norm_of_mem (spectrum_subset_quasispectrum ℝ A hx)).trans hn)⟩
  constructor
  · have hh := cfc_mono (a := A) (f := (X-C 4*(X-X^2) : ℝ[X]).eval)
      (g := window (1/2) (3/4)) (fun x hx => by
        obtain ⟨hx0,hx1⟩ := hb x hx
        simp only [eval_sub,eval_mul,eval_C,eval_X,eval_pow]
        by_cases hx : x≤3/4
        · have hw := window_nonneg (by norm_num : (1/2:ℝ)<3/4) x
          have he := mul_nonneg hx0 (by linarith : 0≤3-4*x)
          nlinarith
        · rw [window_one (by norm_num : (1/2:ℝ)<3/4) (le_of_not_ge hx)]
          have he := mul_nonneg hx0 (by linarith : 0≤1-x)
          nlinarith)
      (X-C 4*(X-X^2) : ℝ[X]).continuous.continuousOn
      (window_continuous (by norm_num : (1/2:ℝ)<3/4)).continuousOn
    simpa only [cfc_polynomial _ A hA,map_sub,map_mul,map_pow,aeval_X,aeval_C,
      ← Algebra.smul_def] using hh
  · have hh := cfc_mono (a := A) (f := window (1/4) (1/2))
      (g := (X+C 4*(X-X^2) : ℝ[X]).eval) (fun x hx => by
        obtain ⟨hx0,hx1⟩ := hb x hx
        simp only [eval_add,eval_mul,eval_sub,eval_C,eval_X,eval_pow]
        by_cases hx : x≤1/4
        · rw [window_zero hx]
          have he := mul_nonneg hx0 (by linarith : 0≤1-x)
          nlinarith
        · have hw := window_le_one (by norm_num : (1/4:ℝ)<1/2) x
          have he := mul_nonneg (by linarith : 0≤4*x-1) (by linarith : 0≤1-x)
          nlinarith)
      (window_continuous (by norm_num : (1/4:ℝ)<1/2)).continuousOn
      (X+C 4*(X-X^2) : ℝ[X]).continuous.continuousOn
    simpa only [cfc_polynomial _ A hA,map_add,map_mul,map_sub,map_pow,aeval_X,aeval_C,
      ← Algebra.smul_def] using hh

#print axioms window_defect_bounds
end QuantitativeEulerEndpointSpectralWindow
