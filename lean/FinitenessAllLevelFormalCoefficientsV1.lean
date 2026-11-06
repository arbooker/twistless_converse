module

public import FinitenessAllLevelTaylorGrowthV1
public import FinitenessAllLevelEulerEquationRecoveryV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex Metric Set Filter Asymptotics FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelGlobalHeight
  FinitenessAllLevelCoefficientFunctional FinitenessAllLevelTaylorGrowth
  QuantitativeArithmeticRetainedCertificate Function.Periodic
open scoped Topology

variable {N Q p : ℕ} {hQ : 0 < Q}

/-- The descended cusp function agrees with the original disk input on
its whole open disk, including zero. -/
theorem initial_cusp_agree (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) (radius a)) :
    extend F.val w = cuspFunction 1 (formal A P a χ m lam F) w := by
  by_cases hw0 : w = 0
  · subst w
    rw [F.property.2, cuspFunction_zero_of_zero_at_inf (by norm_num)
      (formal_zero_at_inf A P a χ m lam F)]
  · have hi : a < (invQParam 1 w).im := by
      apply (norm_qParam_lt_iff (by norm_num : (0 : ℝ) < 1) a _).mp
      rw [qParam_right_inv (by norm_num) hw0, div_one]
      simpa only [mem_ball, dist_zero_right, radius] using hw
    rw [cuspFunction_eq_of_nonzero _ _ hw0, formal_above A P a χ m lam F hi.le]
    change extend F.val w = extend F.val (qParam 1 (invQParam 1 w))
    rw [qParam_right_inv (by norm_num) hw0]

/-- The continuous coefficient functionals coincide with the actual
polynomially bounded Taylor coefficients of the global cusp function. -/
theorem coefficients_of_height (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a))
    (he : FinitenessAllLevelCauchyConstraints.CauchyIdentities (formal A P a χ m lam F))
    {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z : ℂ, 0 < z.im → z.im ^ d * ‖formal A P a χ m lam F z‖ ≤ M) :
    (fun n => coefficientCLM (radius_pos a) n F) =
      taylor (cuspFunction 1 (formal A P a χ m lam F)) ∧
    FinitenessPolynomialSeries.PolynomialBound (fun n => coefficientCLM (radius_pos a) n F) ∧
    ∀ z : ℂ, 0 < z.im → FinitenessFourierConstruction.fourier
      (fun n => coefficientCLM (radius_pos a) n F) z = formal A P a χ m lam F z := by
  obtain ⟨hG, h0, hq⟩ := formal_cusp_holomorphic hN hp A P ha hae χ m lam F he
  have hpoly := polynomialBound hG h0 (fun z _ => (hq z).symm) hM hb
  have hc : (fun n => coefficientCLM (radius_pos a) n F) =
      taylor (cuspFunction 1 (formal A P a χ m lam F)) := by
    funext n
    apply coefficient_eq_of_series (radius_pos a) F hpoly
    intro w hw
    rw [initial_cusp_agree A P a χ m lam F hw]
    exact (sum_taylor hG (ball_subset_ball (radius_lt_one ha).le hw)).symm
  refine ⟨hc, hc ▸ hpoly, fun z hz => ?_⟩
  rw [hc]
  exact (sum_taylor hG (by simpa only [mem_ball, dist_zero_right] using
    (norm_qParam_lt_one (by norm_num : (0 : ℝ) < 1) hz))).trans (hq z)

/-- Positive-weight normalization preserves an individual polynomial
bound and supplies the positive exponent required by literal EulerData. -/
theorem normalized_growth_of_polynomial {R : ℝ} (hR : 0 < R) {k : ℕ} (hk : 0 < k)
    (F : space R)
    (hc : FinitenessPolynomialSeries.PolynomialBound (fun n => coefficientCLM hR n F)) :
    ∃ σ : ℝ, 0 < σ ∧ (fun n => normalizedCLM hR k n F) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ σ) := by
  obtain ⟨C, hC, d, hb⟩ := hc
  refine ⟨(d : ℝ) + 1, by positivity, IsBigO.of_bound (2 * C) ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hα : 0 ≤ FinitenessCompletedNormalization.alpha k := by
    unfold FinitenessCompletedNormalization.alpha
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hpow : 1 ≤ (n : ℝ) ^ FinitenessCompletedNormalization.alpha k :=
    Real.one_le_rpow hn1 hα
  have hnorm : ‖normalizedCLM hR k n F‖ ≤ ‖coefficientCLM hR n F‖ := by
    simp only [normalizedCLM, smul_apply, smul_eq_mul, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (zero_le_one.trans hpow)]
    exact mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ (by linarith)).mpr hpow)
  have hd : 1 ≤ (n : ℝ) ^ d := one_le_pow₀ hn1
  have hd' : (n : ℝ) ^ d ≤ (n : ℝ) ^ (d + 1) := pow_le_pow_right₀ hn1 (Nat.le_succ d)
  have he : (n : ℝ) ^ ((d : ℝ) + 1) = (n : ℝ) ^ (d + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Real.rpow_natCast (n : ℝ) (d + 1))
  rw [Real.norm_eq_abs, he, abs_of_nonneg (pow_nonneg (zero_le_one.trans hn1) _)]
  exact hnorm.trans ((hb n).trans (by nlinarith))

#print axioms initial_cusp_agree
#print axioms coefficients_of_height
#print axioms normalized_growth_of_polynomial

end FinitenessAllLevelFormalContinuation
