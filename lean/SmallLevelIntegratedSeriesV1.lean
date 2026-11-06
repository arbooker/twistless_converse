module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor

open Complex Filter Set MeasureTheory FormalMultilinearSeries
open scoped NNReal ENNReal Topology

/-- Integrating a uniformly dominated scalar power series preserves its
half-unit convergence disk and integrates every coefficient. The bound is
integrable in the parameter, so the interchange is justified. -/
theorem integrated_series {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (a : ℕ → Y → ℂ) (F : Y → ℂ → ℂ) (b : Y → ℝ)
    (hb : Integrable b μ)
    (ha : ∀ n, AEStronglyMeasurable (a n) μ)
    (hab : ∀ n, ∀ᵐ y ∂μ, ‖a n y‖≤b y*2^n)
    (hF : ∀ u : ℂ, ‖u‖<1/2 → ∀ᵐ y ∂μ, HasSum (fun n => a n y*u^n) (F y u)) :
    HasFPowerSeriesOnBall (fun u => ∫ y, F y u ∂μ)
      (ofScalars ℂ (fun n => ∫ y, a n y ∂μ)) 0 ((1/2:ℝ≥0):ℝ≥0∞) := by
  have hcoeff (n : ℕ) : ‖∫ y, a n y ∂μ‖≤(∫ y, b y ∂μ)*2^n := by
    have h := norm_integral_le_of_norm_le (hb.mul_const (2^n)) (hab n)
    simpa only [integral_mul_const] using h
  refine ⟨?_,by norm_num,?_⟩
  · apply (ofScalars ℂ (fun n => ∫ y, a n y ∂μ)).le_radius_of_bound (∫ y, b y ∂μ)
    intro n
    rw [ofScalars_norm]
    have h := mul_le_mul_of_nonneg_right (hcoeff n) (pow_nonneg (by norm_num : (0:ℝ)≤1/2) n)
    simpa only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,one_div,
      NNReal.coe_inv,mul_assoc,← mul_pow,mul_inv_cancel₀ (by norm_num : (2:ℝ)≠0),one_pow,mul_one] using h
  · intro u hu
    have hu' : ‖u‖<1/2 := by
      rw [Metric.eball_coe] at hu
      simpa only [Metric.mem_ball,dist_zero_right,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using hu
    let q : ℝ := 2*‖u‖
    have hq0 : 0≤q := by dsimp [q]; positivity
    have hq1 : q<1 := by dsimp [q]; linarith
    have hqsum : Summable (fun n : ℕ => q^n) :=
      summable_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs,abs_of_nonneg hq0] using hq1)
    have hbound (n : ℕ) : ∀ᵐ y ∂μ, ‖a n y*u^n‖≤b y*q^n := by
      filter_upwards [hab n] with y hy
      rw [norm_mul,norm_pow]
      calc
        _≤(b y*2^n)*‖u‖^n := mul_le_mul_of_nonneg_right hy (by positivity)
        _=b y*q^n := by dsimp [q]; rw [mul_pow]; ring
    have hbi : Integrable (fun y => ∑' n : ℕ, b y*q^n) μ := by
      simp_rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq1]
      exact hb.mul_const _
    have hsum := hasSum_integral_of_dominated_convergence
      (fun n y => b y*q^n) (fun n => (ha n).mul_const (u^n)) hbound
      (Filter.Eventually.of_forall (fun y => hqsum.mul_left (b y))) hbi (hF u hu')
    simpa only [ofScalars_apply_eq,smul_eq_mul,integral_mul_const,zero_add] using hsum

#print axioms integrated_series

end SmallLevelTaylor
