module

public import FinitenessEulerRecurrenceV1
public import AsymptoticRamifiedCoefficientsV1

set_option autoImplicit false
@[expose] public section

namespace FinitenessAllLevelGoodCoefficients

open FinitenessOriginalInput FinitenessOriginalFourier

/-- The unramified Hecke recurrence follows from the literal Euler product,
including at indices divisible by the prime. -/
theorem good_mul {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hgood : ¬ p ∣ N) (n : ℕ) :
    f (p * n) = f p * f n - (if p ∣ n then f (n / p) else 0) := by
  obtain ⟨_, hm, hr⟩ := FinitenessEulerIdentification.euler_arithmetic hf
  have h := FinitenessEulerRecurrence.full_recurrence f
    (fun q => if q ∣ N then 0 else 1) hf.zero hm hr hp n
  simp only [ite_eq_right hgood] at h
  split_ifs with hd
  · simpa only [ite_eq_left hd, one_mul] using eq_sub_of_add_eq h
  · simpa only [ite_eq_right hd, zero_mul] using eq_sub_of_add_eq h

/-- The normalized Fourier coefficients have two terms at a good prime.
The second term is the coefficient insertion for dilation by p. -/
theorem fullCoefficients_good_mul {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hgood : ¬ p ∣ N) (k n : ℕ) :
    fullCoefficients f k (p * n) =
      (f p * ((p : ℝ) ^ FinitenessCompletedNormalization.alpha k : ℝ)) *
        fullCoefficients f k n -
      (((p : ℝ) ^ FinitenessCompletedNormalization.alpha k : ℝ) : ℂ) ^ 2 *
        (if p ∣ n then fullCoefficients f k (n / p) else 0) := by
  rw [fullCoefficients, FinitenessGrowthNormalization.normalized, good_mul hf hp hgood]
  simp only [FinitenessGrowthNormalization.normalized,
    Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg n),
    Complex.ofReal_mul]
  by_cases hd : p ∣ n
  · rw [ite_eq_left hd, ite_eq_left hd]
    have he : (n : ℝ) ^ FinitenessCompletedNormalization.alpha k =
        (p : ℝ) ^ FinitenessCompletedNormalization.alpha k *
          ((n / p : ℕ) : ℝ) ^ FinitenessCompletedNormalization.alpha k := by
      conv_lhs => rw [← Nat.mul_div_cancel' hd]
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg _)]
    rw [he, Complex.ofReal_mul]
    ring
  · rw [ite_eq_right hd, ite_eq_right hd]
    ring

#print axioms good_mul
#print axioms fullCoefficients_good_mul

end FinitenessAllLevelGoodCoefficients
