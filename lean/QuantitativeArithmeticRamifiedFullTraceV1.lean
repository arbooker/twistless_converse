module

public import AsymptoticRamifiedFourierV1
public import AsymptoticRamifiedCoefficientsV1
public import QuantitativeArithmeticRetainedReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace QuantitativeArithmeticRamifiedFullTrace

open Complex FinitenessFourierConstruction FinitenessPolynomialSeries
  FinitenessOriginalInput FinitenessOriginalFourier
  QuantitativeArithmeticRetainedReconstruction

theorem dilation_height {p : ℕ} (hp : 0 < p) {z : ℂ} (hz : 0 < z.im) :
    0 < ((p : ℂ) * z).im := by
  simpa only [mul_im, natCast_re, natCast_im, zero_mul, add_zero] using
    mul_pos (show (0 : ℝ) < p by exact_mod_cast hp) hz

/-- Complete additive averaging is Fourier projection onto the indices
divisible by the averaging modulus, with the literal unnormalised factor p. -/
theorem complete_projection (a : ℕ → ℂ) (ha : PolynomialBound a)
    {p : ℕ} (hp : 0 < p) {z : ℂ} (hz : 0 < z.im) :
    completeTwist (fourier a) p z =
      (p : ℂ) * fourier (fun n => a (p * n)) ((p : ℂ) * z) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have he (b : ℕ) : ((p : ℂ) * z + (b : ℂ)) / p = z + (b : ℂ) / p := by
    field_simp
  simpa only [completeTwist, he] using
    AsymptoticRamifiedFourier.average a ha hp (dilation_height hp hz)

/-- A coefficient recurrence gives the complete-row equation used by the
retained-row reconstruction theorem. -/
theorem complete_of_row (a : ℕ → ℂ) (ha : PolynomialBound a)
    {p : ℕ} (hp : 0 < p) (c : ℂ) (hc : ∀ n, a (p * n) = c * a n)
    {z : ℂ} (hz : 0 < z.im) :
    completeTwist (fourier a) p z =
      ((p : ℂ) * c) * fourier a ((p : ℂ) * z) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have he (b : ℕ) : ((p : ℂ) * z + (b : ℂ)) / p = z + (b : ℂ) / p := by
    field_simp
  simpa only [completeTwist, he] using
    AsymptoticRamifiedFourier.average_of_row a ha hp c hc (dilation_height hp hz)

/-- The original Euler product supplies every retained prime row, without
any new eigenvalue or functional-equation assumption. -/
theorem original_complete {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (k : ℕ)
    {z : ℂ} (hz : 0 < z.im) :
    completeTwist (fourier (fullCoefficients f k)) p z =
      ((p : ℂ) * fullCoefficients f k p) *
        fourier (fullCoefficients f k) ((p : ℂ) * z) := by
  obtain ⟨τ, _, hg⟩ := hf.growth
  apply complete_of_row _ (polynomial_bound hf.zero hg k) hp.pos _ _ hz
  intro n
  exact AsymptoticRamifiedCoefficients.fullCoefficients_bad_mul hf hp hpN k n

/-- At positive even weight 2m the retained multiplier is delta_p p^m,
where delta_p is the actual normalized ramified Euler parameter. -/
noncomputable def multiplier (f : ℕ → ℂ) (m p : ℕ) : ℂ :=
  (f p * (Real.sqrt p : ℂ)) * (p : ℂ) ^ m

theorem original_complete_even_succ {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (h : ℕ)
    {z : ℂ} (hz : 0 < z.im) :
    completeTwist (fourier (fullCoefficients f (2 * (h + 1)))) p z =
      multiplier f (h + 1) p *
        fourier (fullCoefficients f (2 * (h + 1))) ((p : ℂ) * z) := by
  obtain ⟨τ, _, hg⟩ := hf.growth
  rw [complete_of_row _ (polynomial_bound hf.zero hg _) hp.pos _
    (AsymptoticRamifiedCoefficients.simple_relation hf hp hpN h) hz]
  simp only [multiplier, pow_succ]
  ring

theorem original_complete_even {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) {m : ℕ} (hm : 0 < m)
    {z : ℂ} (hz : 0 < z.im) :
    completeTwist (fourier (fullCoefficients f (2 * m))) p z =
      multiplier f m p * fourier (fullCoefficients f (2 * m)) ((p : ℂ) * z) := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact original_complete_even_succ hf hp hpN h hz

theorem multiplier_square {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpsq : p ^ 2 ∣ N) (m : ℕ) :
    multiplier f m p = 0 := by
  simp [multiplier, FinitenessOriginalTwistLocal.bad_parameter_zero hf hp hpsq]

theorem multiplier_simple {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬p ^ 2 ∣ N) (m : ℕ) :
    multiplier f m p = (p : ℂ) ^ m ∨ multiplier f m p = -(p : ℂ) ^ m := by
  rcases AsymptoticRamifiedCoefficients.simple_sign hf hp hpN hpsq with h | h
  · exact Or.inl (by simp [multiplier, h])
  · exact Or.inr (by simp [multiplier, h])

/-- The complete-row multiplier has the uniform weight bound needed for
upward-dilation contraction. This also includes all highly ramified primes. -/
theorem multiplier_norm_le {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (m : ℕ) :
    ‖multiplier f m p‖ ≤ (p : ℝ) ^ m := by
  by_cases hpsq : p ^ 2 ∣ N
  · rw [multiplier_square hf hp hpsq, norm_zero]
    positivity
  · rcases multiplier_simple hf hp hpN hpsq m with h | h
    · simp [h, norm_pow]
    · simp [h, norm_pow]

theorem multiplier_values {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (m : ℕ) :
    multiplier f m p = 0 ∨ multiplier f m p = (p : ℂ) ^ m ∨
      multiplier f m p = -(p : ℂ) ^ m := by
  by_cases hpsq : p ^ 2 ∣ N
  · exact Or.inl (multiplier_square hf hp hpsq m)
  · exact Or.inr (multiplier_simple hf hp hpN hpsq m)

#print axioms complete_projection
#print axioms complete_of_row
#print axioms original_complete
#print axioms original_complete_even
#print axioms multiplier_norm_le
#print axioms multiplier_values

end QuantitativeArithmeticRamifiedFullTrace
