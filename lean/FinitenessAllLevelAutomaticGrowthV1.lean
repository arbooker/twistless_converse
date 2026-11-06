module

public import FinitenessAllLevelEigenvalueFibersV1
public import FinitenessAllLevelFourierGrowthV1
public import FinitenessPaper2CoefficientBoundsV1

set_option autoImplicit false
@[expose] public section

namespace FinitenessAllLevelAutomaticGrowth

open Complex Filter Asymptotics FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction QuantitativeArithmeticRetainedCertificate
  FinitenessAllLevelGlobalHeight FinitenessAllLevelGoodTrace

theorem original_height {N Q : ℕ} {S : Finset ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (A : Certificate N S Q hQ) {L : ℝ} (P : Parameters A L)
    (hprime : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ N) (hdiv : ∀ p ∈ S, p ∣ Q)
    {m : ℕ} {f : ℕ → ℂ} (hf : IsSolution N (2 * m) f)
    (hlam : ∀ p ∈ S, ‖f p‖ ≤ L) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 0 < z.im →
      z.im ^ (m + P.s) * ‖fourier (fullCoefficients f (2 * m)) z‖ ≤ M := by
  obtain ⟨χ, _, hχ, hFE⟩ := FinitenessOriginalTwistedContinuations.solution_laws hN hQ hf
  obtain ⟨τ, _, hg⟩ := hf.growth
  have ha := polynomial_bound hf.zero hg (2 * m)
  obtain ⟨M, hM, _, hb⟩ := FinitenessAllLevelEnvelope.global_bound hN A P
    (fun p hp => (hprime p hp).1) hdiv _ (periodic _) χ f m
    (fun q _ => hχ q) hlam hFE
    (fun p hp z hz => original_complete_even hf.toEulerData (hprime p hp).1
      (hprime p hp).2 m hz)
    (fun y hy => FinitenessCuspBounds.tail _ (disk (fullCoefficients f (2 * m)))
      (disk_holomorphic ha) (disk_zero (fullCoefficients_zero hf.zero _))
      (fun z hz => (disk_eq_fourier _ hz).symm) (m + P.s) hy)
  exact ⟨M, hM, hb⟩

/-- The power from normalizing the Fourier coefficients cancels the
half-weight in the global bound, leaving a weight-independent exponent. -/
theorem growth_of_height {N m s : ℕ} {f : ℕ → ℂ} (hf : IsSolution N (2 * m) f)
    {M : ℝ} (hbound : ∀ z : ℂ, 0 < z.im →
      z.im ^ (m + s) * ‖fourier (fullCoefficients f (2 * m)) z‖ ≤ M) :
    f =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((s : ℝ) + 1 / 2)) := by
  obtain ⟨τ, _, hg⟩ := hf.growth
  apply IsBigO.of_bound (M * Real.exp (2 * Real.pi))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb := FinitenessAllLevelFourierGrowth.coefficient_polynomial
    (polynomial_bound hf.zero hg (2 * m)) hbound (show 0 < n by omega)
  have he : (n : ℝ) ^ (m + s) =
      (n : ℝ) ^ ((s : ℝ) + 1 / 2) *
        (n : ℝ) ^ FinitenessCompletedNormalization.alpha (2 * m) := by
    rw [← Real.rpow_add hnR, ← Real.rpow_natCast]
    congr 1
    unfold FinitenessCompletedNormalization.alpha
    push_cast
    ring
  simp only [fullCoefficients, FinitenessGrowthNormalization.normalized, norm_mul,
    norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnR.le _)] at hb
  rw [he, ← mul_assoc] at hb
  have hc := (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hnR
    (FinitenessCompletedNormalization.alpha (2 * m)))).mp hb
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnR.le _)] using hc

/-- Automatic normalized coefficient growth from bounded retained
eigenvalues, with exponent chosen before the weight and the solution. -/
theorem automatic_growth {N Q : ℕ} {S : Finset ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (A : Certificate N S Q hQ) {L : ℝ} (P : Parameters A L)
    (hprime : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ N) (hdiv : ∀ p ∈ S, p ∣ Q)
    {m : ℕ} {f : ℕ → ℂ} (hf : IsSolution N (2 * m) f)
    (hlam : ∀ p ∈ S, ‖f p‖ ≤ L) :
    f =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((P.s : ℝ) + 1 / 2)) := by
  obtain ⟨M, _, hb⟩ := original_height hN A P hprime hdiv hf hlam
  exact growth_of_height hf hb

/-- At any level, a bound on one auxiliary eigenvalue supplies a common
growth exponent and a constant-one divisor envelope for every solution.
The chosen exponent is independent of the weight. -/
theorem uniform_coefficient_envelope {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {L : ℝ} (hL : 0 ≤ L) :
    ∃ s : ℕ, ∀ m : ℕ, ∀ f : ℕ → ℂ, IsSolution N (2 * m) f → ‖f p‖ ≤ L →
      (f =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((s : ℝ) + 1 / 2))) ∧
      ∀ n : ℕ, n ≠ 0 → ‖f n‖ ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ ((s : ℝ) + 1 / 2) := by
  obtain ⟨Q, hQ, _hNQ, hpQ, ⟨A⟩⟩ :=
    FinitenessAllLevelAuxiliary.certificate_at_prime hN hp hlarge
  obtain ⟨P⟩ := parameters_exist hN hQ A hL
  refine ⟨P.s, fun m f hf hlam => ?_⟩
  have hg := automatic_growth hN A P
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using And.intro hp hgood)
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hpQ) hf
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hlam)
  refine ⟨hg, fun n hn => ?_⟩
  exact FinitenessPaper2.coefficient_uniform_bound hN
    ((FinitenessPaper2.mem_iff_original N (2 * m) _ f).mpr ⟨hf, hg⟩) hn

#print axioms original_height
#print axioms growth_of_height
#print axioms automatic_growth
#print axioms uniform_coefficient_envelope

end FinitenessAllLevelAutomaticGrowth
