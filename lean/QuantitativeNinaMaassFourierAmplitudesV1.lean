module

public import QuantitativeNinaMaassFirstModeV1
public import QuantitativeNinaMaassEulerArithmeticV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open FinitenessEulerIdentification

/-!
Separate the arithmetic amplitudes from the first height profile using
the proved prime recurrences. This step requires no Bessel expansion:
after rescaling the height and multiplying by sqrt(n), the entire
coefficient sequence is the canonical Euler sequence times its first
entry. The remaining analytic task is to identify the first profile of
an actual Laplace eigenvector with its decaying Bessel solution.
-/

namespace QuantitativeNinaMaass

theorem sqrt_nat_product (m n : ℕ) :
    (Real.sqrt ((m * n : ℕ) : ℝ) : ℂ) =
      (Real.sqrt (m : ℝ) : ℂ) * (Real.sqrt (n : ℝ) : ℂ) := by
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m), Complex.ofReal_mul]

theorem sqrt_nat_ne_zero (n : ℕ) (hn : 0 < n) : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'

theorem divideHeight_one (y : PositiveHeight) : divideHeight 1 (by decide) y = y := by
  apply Subtype.ext
  simp only [divideHeight, Nat.cast_one, div_one]

theorem divideHeight_product (p n : ℕ) (hp : 0 < p) (hn : 0 < n) (y : PositiveHeight) :
    divideHeight p hp (divideHeight n hn y) = divideHeight (p * n) (Nat.mul_pos hp hn) y := by
  apply Subtype.ext
  simp only [divideHeight, Nat.cast_mul]
  ring

theorem multiply_divideHeight_dvd (p n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (hpn : p ∣ n) (y : PositiveHeight) :
    multiplyHeight p hp (divideHeight n hn y) =
      divideHeight (n / p) (Nat.div_pos (Nat.le_of_dvd hn hpn) hp) y := by
  apply Subtype.ext
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (p : ℝ) * (n / p : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hpn
  have hnp : ((n / p : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.div_pos (Nat.le_of_dvd hn hpn) hp).ne'
  change (p : ℝ) * (y.val / n) = y.val / (n / p : ℕ)
  field_simp
  nlinarith [congrArg (fun z : ℝ => y.val * z) he]

def scaledHeightCoefficients (c : HeightCoefficients) (y : PositiveHeight) : ℕ → ℂ :=
  fun n => if hn : 0 < n then (Real.sqrt (n : ℝ) : ℂ) * c n (divideHeight n hn y) else 0

theorem scaledHeightCoefficients_zero (c : HeightCoefficients) (y : PositiveHeight) :
    scaledHeightCoefficients c y 0 = 0 := by simp [scaledHeightCoefficients]

theorem scaledHeightCoefficients_one (c : HeightCoefficients) (y : PositiveHeight) :
    scaledHeightCoefficients c y 1 = c 1 y := by
  simp only [scaledHeightCoefficients, dite_eq_left (by decide : 0 < 1),
    Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, one_mul, divideHeight_one]

theorem euler_indicator (N p n : ℕ) :
    (if p ∣ n then xi N p else 0) = if ¬ p ∣ N ∧ p ∣ n then (1 : ℂ) else 0 := by
  classical
  by_cases hpN : p ∣ N <;> by_cases hpn : p ∣ n <;> simp [xi, hpN, hpn]

/-- Rescaling the physical height removes both square-root normalizations
from every prime relation, including the ramified missing term. -/
theorem scaledHeightCoefficients_recurrence (N : ℕ) (ell : ℕ → ℂ)
    (c : HeightCoefficients) (hc : PrimeHeightEigenrelations N ell c)
    (y : PositiveHeight) (p : ℕ) (hp : p.Prime) (n : ℕ) :
    scaledHeightCoefficients c y (p * n) +
      (if p ∣ n then xi N p else 0) * scaledHeightCoefficients c y (n / p) =
        ell p * scaledHeightCoefficients c y n := by
  by_cases hn : n = 0
  · subst n
    simp only [mul_zero, Nat.zero_div, scaledHeightCoefficients_zero, mul_zero, add_zero]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hpn0 : 0 < p * n := Nat.mul_pos hp.pos hn0
  have ht := hc p hp n (divideHeight n hn0 y)
  rw [divideHeight_product] at ht
  rw [euler_indicator]
  by_cases hi : ¬ p ∣ N ∧ p ∣ n
  · have hnp0 : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn0 hi.2) hp.pos
    have hs : (Real.sqrt (n : ℝ) : ℂ) =
        (Real.sqrt (p : ℝ) : ℂ) * (Real.sqrt ((n / p : ℕ) : ℝ) : ℂ) := by
      rw [← sqrt_nat_product, Nat.mul_div_cancel' hi.2]
    rw [ite_eq_left hi, multiply_divideHeight_dvd p n hp.pos hn0 hi.2] at ht
    simp only [ite_eq_left hi, one_mul, scaledHeightCoefficients,
      dite_eq_left hpn0, dite_eq_left hnp0, dite_eq_left hn0, sqrt_nat_product]
    have hmul := congrArg (fun z : ℂ => (Real.sqrt (n : ℝ) : ℂ) * z) ht
    have hcancel : (Real.sqrt (n : ℝ) : ℂ) * (Real.sqrt (p : ℝ) : ℂ)⁻¹ =
        (Real.sqrt ((n / p : ℕ) : ℝ) : ℂ) := by
      rw [hs]
      field_simp [sqrt_nat_ne_zero p hp.pos]
    rw [mul_add, ← mul_assoc _ _ (c (n / p) _), hcancel] at hmul
    linear_combination -hmul
  · rw [ite_eq_right hi, add_zero] at ht
    simp only [ite_eq_right hi, zero_mul, add_zero, scaledHeightCoefficients,
      dite_eq_left hpn0, dite_eq_left hn0, sqrt_nat_product]
    linear_combination -(Real.sqrt (n : ℝ) : ℂ) * ht

/-- The unnormalized scalar recursion has one free initial value. This
is an induction theorem, not a multiplicity-one assumption. -/
theorem scalar_prime_recurrence_profile (N : ℕ) (ell f : ℕ → ℂ)
    (hf0 : f 0 = 0)
    (hrec : ∀ (p : ℕ), p.Prime → ∀ n,
      f (p * n) + (if p ∣ n then xi N p else 0) * f (n / p) = ell p * f n) :
    ∀ n, f n = canonicalEulerCoefficients N ell n * f 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n = 0
    · subst n
      rw [hf0, canonicalEulerCoefficients_zero, zero_mul]
    by_cases h1 : n = 1
    · subst n
      rw [canonicalEulerCoefficients_one, one_mul]
    obtain ⟨p, hp, m, hpm⟩ := Nat.exists_prime_and_dvd h1
    subst n
    have hm : 0 < m := by
      by_contra h
      have hm0 : m = 0 := by omega
      exact h0 (by rw [hm0, mul_zero])
    have hmn : m < p * m := by nlinarith [hp.two_le]
    have h := hrec p hp m
    rw [ih m hmn, ih (m / p) (lt_of_le_of_lt (Nat.div_le_self m p) hmn)] at h
    have k := canonicalEulerCoefficients_full_recurrence N ell p hp m
    linear_combination h - f 1 * k

theorem scaledHeightCoefficients_factorization (N : ℕ) (ell : ℕ → ℂ)
    (c : HeightCoefficients) (hc : PrimeHeightEigenrelations N ell c)
    (y : PositiveHeight) (n : ℕ) :
    scaledHeightCoefficients c y n = canonicalEulerCoefficients N ell n * c 1 y := by
  simpa only [scaledHeightCoefficients_one] using scalar_prime_recurrence_profile
    N ell (scaledHeightCoefficients c y) (scaledHeightCoefficients_zero c y)
    (scaledHeightCoefficients_recurrence N ell c hc y) n

/-- Every positive height profile is determined by the first profile and
the canonical Euler coefficients, with the exact sqrt(n) normalization. -/
theorem prime_height_profile_factorization (N : ℕ) (ell : ℕ → ℂ)
    (c : HeightCoefficients) (hc : PrimeHeightEigenrelations N ell c)
    (n : ℕ) (hn : 0 < n) (y : PositiveHeight) :
    (Real.sqrt (n : ℝ) : ℂ) * c n y =
      canonicalEulerCoefficients N ell n * c 1 (multiplyHeight n hn y) := by
  have h := scaledHeightCoefficients_factorization N ell c hc (multiplyHeight n hn y) n
  simpa only [scaledHeightCoefficients, dite_eq_left hn, divide_multiplyHeight] using h

/-- At any nonzero first-profile height, the normalized rescaled sequence
is the same canonical sequence. The choice of height introduces no new
arithmetic data. -/
theorem normalized_height_coefficients (N : ℕ) (ell : ℕ → ℂ)
    (c : HeightCoefficients) (hc : PrimeHeightEigenrelations N ell c)
    (y : PositiveHeight) (hy : c 1 y ≠ 0) :
    (fun n => scaledHeightCoefficients c y n / c 1 y) = canonicalEulerCoefficients N ell := by
  funext n
  rw [scaledHeightCoefficients_factorization N ell c hc y n, mul_div_cancel_right₀ _ hy]

#print axioms sqrt_nat_product
#print axioms sqrt_nat_ne_zero
#print axioms divideHeight_one
#print axioms divideHeight_product
#print axioms multiply_divideHeight_dvd
#print axioms scaledHeightCoefficients_zero
#print axioms scaledHeightCoefficients_one
#print axioms euler_indicator
#print axioms scaledHeightCoefficients_recurrence
#print axioms scalar_prime_recurrence_profile
#print axioms scaledHeightCoefficients_factorization
#print axioms prime_height_profile_factorization
#print axioms normalized_height_coefficients

end QuantitativeNinaMaass
