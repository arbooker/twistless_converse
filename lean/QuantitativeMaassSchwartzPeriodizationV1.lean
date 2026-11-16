module

public import QuantitativeMaassStationaryFourierV1
public import Mathlib.Analysis.Fourier.PoissonSummation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory TopologicalSpace ContinuousMap
open scoped Topology FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- Exact Fourier coefficients of the periodization of a Schwartz profile,
with the unit-period and Fourier-transform conventions made explicit. -/
theorem schwartz_periodized_fourier (F : SchwartzMap ℝ ℂ) (n : ℤ) :
    (∫ x in Icc (0:ℝ) 1,periodCharacter (-n) x*(∑' k : ℤ,F (x+k)))=𝓕 F n := by
  let f : C(ℝ,ℂ) := ⟨F,F.continuous⟩
  have hf (K : Compacts ℝ) :
      Summable (fun k : ℤ => ‖(f.comp (ContinuousMap.addRight k)).restrict K‖) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((isBigO_norm_restrict_cocompact f (by norm_num : (0:ℝ)<2)
        (F.isBigO_cocompact_rpow (-2)) K).comp_tendsto Int.tendsto_coe_cofinite)
  have hh := Real.fourierCoeff_tsum_comp_add hf n
  rw [fourierCoeff_eq_intervalIntegral _ n 0] at hh
  simp only [div_one,one_smul,zero_add] at hh
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc] at hh
  simpa only [periodCharacter,Function.Periodic.lift_coe,zsmul_one,
    ←ContinuousMap.tsum_apply (summable_of_locally_summable_norm hf),
    ContinuousMap.comp_apply,ContinuousMap.coe_addRight,smul_eq_mul,f,
    ContinuousMap.coe_mk,SchwartzMap.fourier_coe] using hh

#print axioms schwartz_periodized_fourier

end QuantitativeMaass
