module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Tactic.Ring

@[expose] public section

namespace FinitenessPolynomialSeries

open Metric FormalMultilinearSeries
open scoped NNReal ENNReal

/-- Integer-exponent envelope for the Fourier coefficients. The exponent
and constant are individual to the sequence, never uniform across S(N,k). -/
def PolynomialBound (a : ℕ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n : ℕ, ‖a n‖ ≤ C*(1+(n : ℝ)^d)

noncomputable def sum (a : ℕ → ℂ) : ℂ → ℂ := ofScalarsSum a

theorem norm_summable {a : ℕ → ℂ} (ha : PolynomialBound a)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : Summable (fun n => ‖a n‖*r^n) := by
  obtain ⟨C,hC,d,hd⟩ := ha
  have hrnorm : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr
  have hsum : Summable (fun n : ℕ => C*(r^n+(n : ℝ)^d*r^n)) :=
    ((summable_geometric_of_norm_lt_one hrnorm).add
      (summable_pow_mul_geometric_of_norm_lt_one d hrnorm)).mul_left C
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 n)) _ hsum
  intro n
  calc
    ‖a n‖*r^n ≤ (C*(1+(n : ℝ)^d))*r^n :=
      mul_le_mul_of_nonneg_right (hd n) (pow_nonneg hr0 n)
    _ = C*(r^n+(n : ℝ)^d*r^n) := by ring

theorem radius_ge_one {a : ℕ → ℂ} (ha : PolynomialBound a) :
    1 ≤ (ofScalars ℂ a).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  apply (ofScalars ℂ a).le_radius_of_summable_norm
  simpa only [ofScalars_norm] using norm_summable ha r.coe_nonneg (by exact_mod_cast hr)

theorem analytic {a : ℕ → ℂ} (ha : PolynomialBound a) :
    AnalyticOnNhd ℂ (sum a) (ball 0 1) := by
  intro w hw
  apply (ofScalars ℂ a).analyticOnNhd
  apply Metric.eball_subset_eball (radius_ge_one ha)
  change w ∈ Metric.eball 0 ((1 : ℝ≥0) : ℝ≥0∞)
  rwa [Metric.eball_coe]

theorem holomorphic {a : ℕ → ℂ} (ha : PolynomialBound a) :
    DifferentiableOn ℂ (sum a) (ball 0 1) := (analytic ha).differentiableOn

theorem zero {a : ℕ → ℂ} (ha0 : a 0 = 0) : sum a 0 = 0 := by
  simp [sum, ofScalarsSum_zero, ha0]

theorem sum_eq_tsum (a : ℕ → ℂ) (w : ℂ) : sum a w = ∑' n : ℕ, a n*w^n := by
  simp only [sum, ofScalars_sum_eq, smul_eq_mul]

theorem summable {a : ℕ → ℂ} (ha : PolynomialBound a) {w : ℂ} (hw : ‖w‖ < 1) :
    Summable (fun n : ℕ => a n*w^n) := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_pow] using norm_summable ha (norm_nonneg w) hw

theorem has_series {a : ℕ → ℂ} (ha : PolynomialBound a) :
    HasFPowerSeriesAt (sum a) (ofScalars ℂ a) 0 :=
  ((ofScalars ℂ a).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num) (radius_ge_one ha))).hasFPowerSeriesAt

theorem coefficients_unique {a b : ℕ → ℂ} (ha : PolynomialBound a) (hb : PolynomialBound b)
    (heq : ∀ w ∈ ball (0 : ℂ) 1, sum a w = sum b w) : a = b := by
  apply ofScalars_series_injective ℂ ℂ
  apply (has_series ha).eq_formalMultilinearSeries_of_eventually (has_series hb)
  exact Filter.mem_of_superset (ball_mem_nhds (0 : ℂ) (by norm_num)) heq

#print axioms radius_ge_one
#print axioms holomorphic
#print axioms summable
#print axioms coefficients_unique

end FinitenessPolynomialSeries
