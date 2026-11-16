module

public import QuantitativeNinaMaassHeckeAlgebraV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open QuantitativeMaass AsymptoticCongruenceStrip AsymptoticClassicalPetersson

/-!
Uniqueness from the literal prime recurrences, before Bessel separation.
The good-prime downward term is omitted exactly at the ramified primes.
This is an intermediate recurrence theorem: construction of an actual
all-prime eigenfamily and its ramified Fourier relations is still required
before applying it to the solution-count lower bound.
-/

namespace QuantitativeNinaMaass

def PrimeHeightEigenrelations (N : ℕ) (ell : ℕ → ℂ) (c : HeightCoefficients) : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n : ℕ) (y : PositiveHeight),
    ell p * c n y = (Real.sqrt (p : ℝ) : ℂ) * c (p * n) (divideHeight p hp.pos y) +
      if ¬ p ∣ N ∧ p ∣ n then
        ((Real.sqrt (p : ℝ) : ℂ)⁻¹) * c (n / p) (multiplyHeight p hp.pos y) else 0

theorem divide_multiplyHeight (p : ℕ) (hp : 0 < p) (y : PositiveHeight) :
    divideHeight p hp (multiplyHeight p hp y) = y := by
  apply Subtype.ext
  change (p : ℝ) * y.val / p = y.val
  exact mul_div_cancel_left₀ y.val (by exact_mod_cast hp.ne')

/-- Prime recurrences propagate a vanishing first profile to every
positive Fourier index. No injectivity or multiplicity-one hypothesis
is used: the descent is ordinary strong induction on the index. -/
theorem prime_height_first_zero (N : ℕ) (ell : ℕ → ℂ) (c : HeightCoefficients)
    (hc : PrimeHeightEigenrelations N ell c) (hfirst : ∀ y, c 1 y = 0) :
    ∀ n, 0 < n → ∀ y, c n y = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn y
    by_cases h1 : n = 1
    · simpa only [h1] using hfirst y
    obtain ⟨p, hp, m, hpm⟩ := Nat.exists_prime_and_dvd h1
    subst n
    have hm : 0 < m := by
      by_contra h
      have hm0 : m = 0 := by omega
      simp only [hm0, mul_zero, lt_self_iff_false] at hn
    have hmn : m < p * m := by nlinarith [hp.two_le]
    have hlower : (if ¬ p ∣ N ∧ p ∣ m then
        (Real.sqrt (p : ℝ) : ℂ)⁻¹ * c (m / p)
          (multiplyHeight p hp.pos (multiplyHeight p hp.pos y)) else 0) = 0 := by
      split_ifs with h
      · rw [ih (m / p) (lt_of_le_of_lt (Nat.div_le_self m p) hmn)
          (Nat.div_pos (Nat.le_of_dvd hm h.2) hp.pos), mul_zero]
      · rfl
    have h := hc p hp m (multiplyHeight p hp.pos y)
    rw [ih m hmn hm, mul_zero, hlower, add_zero, divide_multiplyHeight] at h
    have hs : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)).ne'
    exact (mul_eq_zero.mp h.symm).resolve_left hs

theorem prime_height_relations_sub (N : ℕ) (ell : ℕ → ℂ)
    (c d : HeightCoefficients) (hc : PrimeHeightEigenrelations N ell c)
    (hd : PrimeHeightEigenrelations N ell d) : PrimeHeightEigenrelations N ell (c - d) := by
  intro p hp n y
  have h := hc p hp n y
  have k := hd p hp n y
  by_cases hi : ¬ p ∣ N ∧ p ∣ n
  · simp only [Pi.sub_apply, ite_eq_left hi] at h k ⊢
    linear_combination h - k
  · simp only [Pi.sub_apply, ite_eq_right hi] at h k ⊢
    linear_combination h - k

theorem prime_height_first_unique (N : ℕ) (ell : ℕ → ℂ)
    (c d : HeightCoefficients) (hc : PrimeHeightEigenrelations N ell c)
    (hd : PrimeHeightEigenrelations N ell d) (hfirst : ∀ y, c 1 y = d 1 y) :
    ∀ n, 0 < n → ∀ y, c n y = d n y := by
  have h := prime_height_first_zero N ell (c - d) (prime_height_relations_sub N ell c d hc hd)
    (by intro y; exact sub_eq_zero.mpr (hfirst y))
  intro n hn y
  exact sub_eq_zero.mp (h n hn y)

/-- For actual continuous cusp representatives of fixed physical parity,
the same prime eigenvalues and first profile force equality. This is a
proved consequence of Fourier uniqueness and the displayed recurrences. -/
theorem physical_first_profile_unique (N : ℕ) (hN : 0 < N)
    (f g : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hg : Continuous g.val)
    (hcf : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN)
    (hcg : AutomorphicL2.denseEmbedding _ _ g ∈ localCuspidalSpace N hN)
    (s : ℂ)
    (hsf : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      s • AutomorphicL2.denseEmbedding _ _ f)
    (hsg : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ g) =
      s • AutomorphicL2.denseEmbedding _ _ g)
    (ell : ℕ → ℂ)
    (hrf : PrimeHeightEigenrelations N ell (actualHeightCoefficients f.val))
    (hrg : PrimeHeightEigenrelations N ell (actualHeightCoefficients g.val))
    (hfirst : ∀ y, horocycleFourier f.val 1 y = horocycleFourier g.val 1 y) : f = g := by
  apply physical_positive_coefficients_separate N hN f g hf hg hcf hcg s hsf hsg
  funext n y
  have h := prime_height_first_unique N ell _ _ hrf hrg hfirst (n + 1) (by omega) y
  simpa only [actualHeightCoefficients, horocycleFourier, positiveHorocycleCoefficients,
    Nat.cast_add, Nat.cast_one] using h

#print axioms divide_multiplyHeight
#print axioms prime_height_first_zero
#print axioms prime_height_relations_sub
#print axioms prime_height_first_unique
#print axioms physical_first_profile_unique

end QuantitativeNinaMaass
