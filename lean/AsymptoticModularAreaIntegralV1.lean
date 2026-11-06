module

public import AsymptoticModularBoundaryV1
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticModularDomain

open MeasureTheory Set Real
open scoped ENNReal

theorem sqrt_lower_pos {x : ℝ} (hx : x∈Icc (-(1:ℝ)/2) (1/2)) :
    0<Real.sqrt (1-x^2) := by
  apply Real.sqrt_pos_of_pos
  nlinarith [sq_nonneg (x+1/2),sq_nonneg (x-1/2),mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hx.1)]

theorem inverse_sqrt_continuous :
    ContinuousOn (fun x : ℝ => (Real.sqrt (1-x^2))⁻¹) (Icc (-(1:ℝ)/2) (1/2)) := by
  apply ContinuousOn.inv₀
  · fun_prop
  · intro x hx
    exact (sqrt_lower_pos hx).ne'

theorem arcsin_half : Real.arcsin (1/2)=Real.pi/6 := by
  rw [← Real.sin_pi_div_six,Real.arcsin_sin]
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

theorem inverse_sqrt_interval_integral :
    (∫ x in (-(1:ℝ)/2)..(1/2),(Real.sqrt (1-x^2))⁻¹)=Real.pi/3 := by
  have hi : IntervalIntegrable (fun x : ℝ => (Real.sqrt (1-x^2))⁻¹)
      volume (-(1:ℝ)/2) (1/2) :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le (by norm_num : -(1:ℝ)/2≤1/2)] using inverse_sqrt_continuous)
  have hd : ∀ x∈uIcc (-(1:ℝ)/2) (1/2),
      HasDerivAt Real.arcsin ((Real.sqrt (1-x^2))⁻¹) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    simpa only [one_div] using Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi,
    show -(1:ℝ)/2= -(1/2) by ring,Real.arcsin_neg,arcsin_half]
  ring

/-- The exact integral left after integrating the hyperbolic area
vertically above the unit circle. -/
theorem inverse_sqrt_lintegral :
    (∫⁻ x : ℝ in Ioo (-(1:ℝ)/2) (1/2),ENNReal.ofReal ((Real.sqrt (1-x^2))⁻¹))=
      ENNReal.ofReal (Real.pi/3) := by
  have hi : IntegrableOn (fun x : ℝ => (Real.sqrt (1-x^2))⁻¹)
      (Ioo (-(1:ℝ)/2) (1/2)) :=
    (inverse_sqrt_continuous.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x => by positivity))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num)]
  exact inverse_sqrt_interval_integral

#print axioms sqrt_lower_pos
#print axioms inverse_sqrt_continuous
#print axioms arcsin_half
#print axioms inverse_sqrt_interval_integral
#print axioms inverse_sqrt_lintegral

end AsymptoticModularDomain
