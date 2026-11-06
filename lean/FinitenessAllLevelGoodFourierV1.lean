module

public import QuantitativeArithmeticRamifiedFullTraceV1
public import FinitenessAllLevelGoodCoefficientsV1

set_option autoImplicit false
set_option maxHeartbeats 600000
@[expose] public section

namespace FinitenessAllLevelGoodFourier

open Complex FinitenessFourierConstruction FinitenessPolynomialSeries
  FinitenessOriginalInput FinitenessOriginalFourier
  QuantitativeArithmeticRetainedReconstruction
  QuantitativeArithmeticRamifiedFullTrace

/-- Insert zeros away from the multiples of p, as required by dilation. -/
noncomputable def insert (a : ℕ → ℂ) (p n : ℕ) : ℂ :=
  if p ∣ n then a (n / p) else 0

theorem insert_polynomial {a : ℕ → ℂ} (ha : PolynomialBound a) (p : ℕ) :
    PolynomialBound (insert a p) := by
  obtain ⟨C, hC, d, hd⟩ := ha
  refine ⟨C, hC, d, fun n => ?_⟩
  unfold insert
  split_ifs
  · exact (hd (n / p)).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl (1 : ℝ)) (pow_le_pow_left₀ (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.div_le_self n p) d)) hC)
  · simp only [norm_zero]
    positivity

/-- Dilation of the Fourier series is proved by support reindexing. -/
theorem fourier_insert (a : ℕ → ℂ) {p : ℕ} (hp : 0 < p) (z : ℂ) :
    fourier (insert a p) z = fourier a ((p : ℂ) * z) := by
  simp only [fourier_eq_exp]
  let g : ℕ → ℂ := fun n => insert a p n * exp (2 * Real.pi * I * (n : ℂ) * z)
  have hinj : Function.Injective (fun n : ℕ => p * n) := by
    intro n m he
    exact Nat.eq_of_mul_eq_mul_left hp he
  have hsupp : Function.support g ⊆ Set.range (fun n : ℕ => p * n) := by
    intro n hn
    have hd : p ∣ n := by
      by_contra h
      exact hn (by simp [g, insert, h])
    obtain ⟨m, hm⟩ := hd
    exact ⟨m, hm.symm⟩
  change (∑' n, g n) = _
  rw [← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro n
  simp only [g, insert, ite_eq_left (dvd_mul_right p n), Nat.mul_div_right n hp,
    Nat.cast_mul]
  congr 2
  ring

/-- A two-term coefficient recurrence gives the corresponding two dilations,
with summability established from the original polynomial envelope. -/
theorem fourier_of_row (a : ℕ → ℂ) (ha : PolynomialBound a) {p : ℕ} (hp : 0 < p)
    (c d : ℂ) (hc : ∀ n, a (p * n) = c * a n - d * insert a p n)
    {z : ℂ} (hz : 0 < z.im) :
    fourier (fun n => a (p * n)) z =
      c * fourier a z - d * fourier a ((p : ℂ) * z) := by
  have hs := exp_summable ha hz
  have ht := exp_summable (insert_polynomial ha p) hz
  simp only [mul_assoc] at hs ht
  rw [← fourier_insert a hp z]
  simp only [fourier_eq_exp, hc, sub_mul, mul_assoc]
  rw [Summable.tsum_sub (hs.mul_left c) (ht.mul_left d), tsum_mul_left, tsum_mul_left]

theorem complete_of_two_rows (a : ℕ → ℂ) (ha : PolynomialBound a)
    {p : ℕ} (hp : 0 < p) (c d : ℂ)
    (hc : ∀ n, a (p * n) = c * a n - d * insert a p n)
    {z : ℂ} (hz : 0 < z.im) :
    completeTwist (fourier a) p z =
      ((p : ℂ) * c) * fourier a ((p : ℂ) * z) -
      ((p : ℂ) * d) * fourier a ((p : ℂ) ^ 2 * z) := by
  rw [complete_projection a ha hp hz,
    fourier_of_row a ha hp c d hc (dilation_height hp hz)]
  rw [show (p : ℂ) * ((p : ℂ) * z) = (p : ℂ) ^ 2 * z by ring]
  ring

/-- Complete additive averaging at a good prime, directly from the original
Euler product. No Hecke eigenrelation is assumed. -/
theorem original_complete {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hgood : ¬ p ∣ N) (k : ℕ)
    {z : ℂ} (hz : 0 < z.im) :
    completeTwist (fourier (fullCoefficients f k)) p z =
      ((p : ℂ) * (f p * ((p : ℝ) ^ FinitenessCompletedNormalization.alpha k : ℝ))) *
        fourier (fullCoefficients f k) ((p : ℂ) * z) -
      ((p : ℂ) * (((p : ℝ) ^ FinitenessCompletedNormalization.alpha k : ℝ) : ℂ) ^ 2) *
        fourier (fullCoefficients f k) ((p : ℂ) ^ 2 * z) := by
  obtain ⟨τ, _, hg⟩ := hf.growth
  exact complete_of_two_rows _ (polynomial_bound hf.zero hg k) hp.pos _ _
    (FinitenessAllLevelGoodCoefficients.fullCoefficients_good_mul hf hp hgood k) hz

#print axioms fourier_insert
#print axioms fourier_of_row
#print axioms complete_of_two_rows
#print axioms original_complete

end FinitenessAllLevelGoodFourier
