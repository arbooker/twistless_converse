module

public import FinitenessOriginalFrickeV1
public import FinitenessCuspBoundsV1
public import AsymptoticClassicalMellinSplitV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelAxisDecay

open Complex Filter Asymptotics Set Metric FinitenessPolynomialSeries
  FinitenessFourierConstruction FinitenessDiskDecay Function.Periodic

theorem fourier_exponential {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0 = 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, η ≤ z.im →
      ‖fourier a z‖ ≤ C * Real.exp (-2 * Real.pi * z.im) := by
  let G := FinitenessPolynomialSeries.sum a
  let R := Real.exp (-2 * Real.pi * η)
  have hR : 0 < R := Real.exp_pos _
  have hR1 : R < 1 := Real.exp_lt_one_iff.mpr (by
    have h := mul_pos Real.pi_pos hη
    nlinarith)
  have hsub : closedBall (0 : ℂ) R ⊆ ball 0 1 := closedBall_subset_ball hR1
  have hG : DifferentiableOn ℂ G (ball 0 1) := FinitenessPolynomialSeries.holomorphic ha
  have hzero : G 0 = 0 := FinitenessPolynomialSeries.zero ha0
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    ((quotient_differentiable G hG 1).continuousOn.mono hsub)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simpa using hR.le))
  have hfactor (w : ℂ) : G w = w * quotient 1 G w := by
    simpa only [pow_one] using zero_coeff_factor G 1
      (fun i hi => by
        have hi0 : i = 0 := by omega
        subst i
        exact hzero) w
  refine ⟨C, hC0, fun z hz => ?_⟩
  have hq : ‖qParam 1 z‖ ≤ R := by
    rw [norm_qParam, div_one]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  change ‖G (qParam 1 z)‖ ≤ _
  rw [hfactor, norm_mul, norm_qParam, div_one]
  calc
    _ ≤ Real.exp (-2 * Real.pi * z.im) * C := mul_le_mul_of_nonneg_left
      (hC _ (by simpa using hq)) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

def axis (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  fourier a (((t / Real.sqrt N : ℝ) : ℂ) * I)

theorem axis_continuous {N : ℕ} (hN : 0 < N) {a : ℕ → ℂ} (ha : PolynomialBound a) :
    ContinuousOn (axis N a) (Ioi 0) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  intro t ht
  apply ContinuousAt.continuousWithinAt
  exact (FinitenessFourierConstruction.holomorphic ha
    (by simpa only [mul_I_im, ofReal_re] using div_pos ht hs)).continuousAt.comp
    (by fun_prop)

theorem axis_exponential {N : ℕ} (hN : 0 < N) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0 = 0) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ t : ℝ, 1 ≤ t →
      ‖axis N a t‖ ≤ C * Real.exp (-c * t) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  obtain ⟨C, hC, hb⟩ := fourier_exponential ha ha0 (one_div_pos.mpr hs)
  refine ⟨C, 2 * Real.pi / Real.sqrt N, hC, by positivity, fun t ht => ?_⟩
  have h := hb (((t / Real.sqrt N : ℝ) : ℂ) * I) (by
    simpa only [mul_I_im, ofReal_re] using div_le_div_of_nonneg_right ht hs.le)
  have he : -(2 * Real.pi / Real.sqrt N) * t = -2 * Real.pi * (t / Real.sqrt N) := by ring
  simpa only [axis, mul_I_im, ofReal_re, he] using h

theorem axis_rapid {N : ℕ} (hN : 0 < N) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0 = 0) (r : ℝ) :
    axis N a =O[atTop] (fun t : ℝ => t ^ r) := by
  obtain ⟨C, c, _, hc, hb⟩ := axis_exponential hN ha ha0
  have ho : axis N a =O[atTop] (fun t : ℝ => Real.exp (-c * t)) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop 1] with t ht
    simpa only [Real.norm_eq_abs, Real.abs_exp] using hb t ht
  exact ho.trans (isLittleO_exp_neg_mul_rpow_atTop hc r).isBigO

#print axioms fourier_exponential
#print axioms axis_continuous
#print axioms axis_exponential
#print axioms axis_rapid

end FinitenessAllLevelAxisDecay
