module

public import AsymptoticClassicalEulerProductV1
public import FinitenessEulerRecurrenceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter Asymptotics
open FinitenessEulerIdentification FinitenessEulerCoefficients FinitenessEulerLocal

/-!
Arithmetic construction from prime eigenvalues. The sequence is defined
by the canonical reciprocal quadratic factors, including the missing
quadratic term at primes dividing the level. Its full recurrences,
multiplicativity, polynomial growth and literal complex HasProd follow
from the existing general arithmetic lemmas.

The identification lemma below requires only the scalar prime recurrence
and normalization, not multiplicativity or an Euler-product premise.
Applying it to Maass eigenfunctions still requires the physical Fourier
amplitude construction. No functional equation or solution count is
claimed in this intermediate chapter.
-/

namespace QuantitativeNinaMaass

def canonicalEulerCoefficients (N : ℕ) (ell : ℕ → ℂ) : ℕ → ℂ := value ell (xi N)

theorem canonicalEulerCoefficients_zero (N : ℕ) (ell : ℕ → ℂ) :
    canonicalEulerCoefficients N ell 0 = 0 := value_zero _ _

theorem canonicalEulerCoefficients_one (N : ℕ) (ell : ℕ → ℂ) :
    canonicalEulerCoefficients N ell 1 = 1 := value_one _ _

theorem canonicalEulerCoefficients_prime (N : ℕ) (ell : ℕ → ℂ) (p : ℕ) (hp : p.Prime) :
    canonicalEulerCoefficients N ell p = ell p := by
  simpa only [canonicalEulerCoefficients, pow_one, coeff] using value_prime_pow ell (xi N) hp 1

theorem canonicalEulerCoefficients_multiplicative (N : ℕ) (ell : ℕ → ℂ)
    (m n : ℕ) (hc : m.Coprime n) :
    canonicalEulerCoefficients N ell (m * n) =
      canonicalEulerCoefficients N ell m * canonicalEulerCoefficients N ell n :=
  FinitenessEulerCoefficients.multiplicative _ _ hc

theorem canonicalEulerCoefficients_prime_power (N : ℕ) (ell : ℕ → ℂ)
    (p : ℕ) (hp : p.Prime) (j : ℕ) :
    canonicalEulerCoefficients N ell (p ^ (j + 2)) =
      canonicalEulerCoefficients N ell p * canonicalEulerCoefficients N ell (p ^ (j + 1)) -
        xi N p * canonicalEulerCoefficients N ell (p ^ j) := by
  rw [canonicalEulerCoefficients_prime N ell p hp]
  simp only [canonicalEulerCoefficients, value_prime_pow ell (xi N) hp, coeff]

theorem canonicalEulerCoefficients_full_recurrence (N : ℕ) (ell : ℕ → ℂ)
    (p : ℕ) (hp : p.Prime) (n : ℕ) :
    canonicalEulerCoefficients N ell (p * n) +
      (if p ∣ n then xi N p else 0) * canonicalEulerCoefficients N ell (n / p) =
        ell p * canonicalEulerCoefficients N ell n := by
  have h := FinitenessEulerRecurrence.full_recurrence
    (canonicalEulerCoefficients N ell) (xi N) (canonicalEulerCoefficients_zero N ell)
    (canonicalEulerCoefficients_multiplicative N ell)
    (canonicalEulerCoefficients_prime_power N ell) hp n
  rwa [canonicalEulerCoefficients_prime N ell p hp] at h

/-- A normalized scalar prime recurrence determines the canonical Euler
coefficients by descent on the index. Multiplicativity is not an input. -/
theorem eq_canonicalEulerCoefficients (N : ℕ) (ell f : ℕ → ℂ)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hrec : ∀ (p : ℕ), p.Prime → ∀ n,
      f (p * n) + (if p ∣ n then xi N p else 0) * f (n / p) = ell p * f n) :
    f = canonicalEulerCoefficients N ell := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n = 0
    · subst n
      exact hf0.trans (canonicalEulerCoefficients_zero N ell).symm
    by_cases h1 : n = 1
    · subst n
      exact hf1.trans (canonicalEulerCoefficients_one N ell).symm
    obtain ⟨p, hp, m, hpm⟩ := Nat.exists_prime_and_dvd h1
    subst n
    have hm : 0 < m := by
      by_contra h
      have hm0 : m = 0 := by omega
      exact h0 (by rw [hm0, mul_zero])
    have hmn : m < p * m := by nlinarith [hp.two_le]
    have hsmall := ih (m / p) (lt_of_le_of_lt (Nat.div_le_self m p) hmn)
    have h := hrec p hp m
    rw [ih m hmn, hsmall] at h
    exact add_right_cancel (h.trans (canonicalEulerCoefficients_full_recurrence N ell p hp m).symm)

/-- A crude uniform prime norm bound already gives exponent two for the
constructed coefficients. No Ramanujan estimate is used. -/
theorem canonicalEulerCoefficients_bound (N : ℕ) (ell : ℕ → ℂ)
    (hell : ∀ p : ℕ, p.Prime → ‖ell p‖ ≤ (p : ℝ) + 1) (n : ℕ) :
    ‖canonicalEulerCoefficients N ell n‖ ≤ (n : ℝ) ^ 2 := by
  apply value_bound ell (xi N) 2 (fun p _ => xi_bound N p)
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h := hell p hp
  nlinarith

theorem canonicalEulerCoefficients_growth (N : ℕ) (ell : ℕ → ℂ)
    (hell : ∀ p : ℕ, p.Prime → ‖ell p‖ ≤ (p : ℝ) + 1) :
    canonicalEulerCoefficients N ell =O[atTop] (fun n : ℕ => (n : ℝ) ^ (2 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall ?_)
  intro n
  simpa only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (n : ℝ)), one_mul]
    using canonicalEulerCoefficients_bound N ell hell n

/-- The actual HasProd required in the original hypotheses, on a complex
right half-plane, follows from the constructed sequence and its norm bound. -/
theorem canonicalEulerCoefficients_eulerProduct (N : ℕ) (ell : ℕ → ℂ)
    (hell : ∀ p : ℕ, p.Prime → ‖ell p‖ ≤ (p : ℝ) + 1) :
    FinitenessOriginalInput.EulerProduct N (canonicalEulerCoefficients N ell) :=
  AsymptoticClassicalEulerProduct.eulerProduct_of_arithmetic
    (canonicalEulerCoefficients_zero N ell) (canonicalEulerCoefficients_one N ell)
    (canonicalEulerCoefficients_growth N ell hell)
    (canonicalEulerCoefficients_multiplicative N ell)
    (canonicalEulerCoefficients_prime_power N ell)

theorem canonicalEulerCoefficients_bad (N : ℕ) (ell : ℕ → ℂ)
    (hbad : ∀ p : ℕ, p.Prime → p ∣ N →
      ell p ^ 2 = if p ^ 2 ∣ N then 0 else (p : ℂ)⁻¹) :
    FinitenessOriginalInput.BadPrimeConditions N (canonicalEulerCoefficients N ell) := by
  intro p hp hpN
  rw [canonicalEulerCoefficients_prime N ell p hp]
  exact hbad p hp hpN

/-- This is the arithmetic part of the original solution predicate.
Its inputs are bounds and quadratic equations for prime eigenvalues;
the literal Euler product and global coefficient growth are conclusions. -/
theorem canonicalEulerCoefficients_eulerData (N : ℕ) (ell : ℕ → ℂ)
    (hell : ∀ p : ℕ, p.Prime → ‖ell p‖ ≤ (p : ℝ) + 1)
    (hbad : ∀ p : ℕ, p.Prime → p ∣ N →
      ell p ^ 2 = if p ^ 2 ∣ N then 0 else (p : ℂ)⁻¹) :
    FinitenessOriginalInput.EulerData N (canonicalEulerCoefficients N ell) :=
  { zero := canonicalEulerCoefficients_zero N ell
    growth := ⟨2, by norm_num, canonicalEulerCoefficients_growth N ell hell⟩
    euler := canonicalEulerCoefficients_eulerProduct N ell hell
    bad := canonicalEulerCoefficients_bad N ell hbad }

/-- For normalized physical amplitudes, it suffices to derive the prime
recurrence. No multiplicativity, global growth or Euler-product assumption
needs to be added to the eigenfunction input. -/
theorem eulerData_of_scalar_prime_recurrences (N : ℕ) (ell f : ℕ → ℂ)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hrec : ∀ (p : ℕ), p.Prime → ∀ n,
      f (p * n) + (if p ∣ n then xi N p else 0) * f (n / p) = ell p * f n)
    (hell : ∀ p : ℕ, p.Prime → ‖ell p‖ ≤ (p : ℝ) + 1)
    (hbad : ∀ p : ℕ, p.Prime → p ∣ N →
      ell p ^ 2 = if p ^ 2 ∣ N then 0 else (p : ℂ)⁻¹) :
    FinitenessOriginalInput.EulerData N f := by
  rw [eq_canonicalEulerCoefficients N ell f hf0 hf1 hrec]
  exact canonicalEulerCoefficients_eulerData N ell hell hbad

#print axioms canonicalEulerCoefficients_zero
#print axioms canonicalEulerCoefficients_one
#print axioms canonicalEulerCoefficients_prime
#print axioms canonicalEulerCoefficients_multiplicative
#print axioms canonicalEulerCoefficients_prime_power
#print axioms canonicalEulerCoefficients_full_recurrence
#print axioms eq_canonicalEulerCoefficients
#print axioms canonicalEulerCoefficients_bound
#print axioms canonicalEulerCoefficients_growth
#print axioms canonicalEulerCoefficients_eulerProduct
#print axioms canonicalEulerCoefficients_bad
#print axioms canonicalEulerCoefficients_eulerData
#print axioms eulerData_of_scalar_prime_recurrences

end QuantitativeNinaMaass
