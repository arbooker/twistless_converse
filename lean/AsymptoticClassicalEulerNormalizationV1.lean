module

public import AsymptoticClassicalFourierNormalizationV1
public import AsymptoticClassicalEulerProductV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalLSeries

open UpperHalfPlane AsymptoticClassicalCusp

variable {N : ℕ} {k : ℤ}

/-- Unitary normalization preserves coprime multiplicativity. -/
theorem coefficients_multiplicative (f : CuspForm (level N) k)
    (hmul : ∀ m n, m.Coprime n → (qExpansion 1 f).coeff (m*n) =
      (qExpansion 1 f).coeff m * (qExpansion 1 f).coeff n)
    (m n : ℕ) (hc : m.Coprime n) :
    coefficients f (m*n) = coefficients f m * coefficients f n := by
  simp only [coefficients, hmul m n hc, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n), Complex.ofReal_mul]
  ring

/-- At prime powers the unitary normalization is a geometric rescaling. -/
theorem coefficients_prime_pow (f : CuspForm (level N) k) (p j : ℕ) :
    coefficients f (p^j) = (qExpansion 1 f).coeff (p^j) *
      (((p : ℝ)^(-((k : ℝ)-1)/2) : ℝ) : ℂ)^j := by
  rw [coefficients, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg p),
    Complex.ofReal_pow]

/-- The factor `p^(k-1)` in the classical Hecke recurrence disappears
under the unitary normalization used in the paper. -/
theorem coefficients_prime_recurrence (f : CuspForm (level N) k)
    (p : ℕ) (hp : 0 < p) (j : ℕ) (ξ : ℂ)
    (hrec : (qExpansion 1 f).coeff (p^(j+2)) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff (p^(j+1)) -
        ξ * (p : ℂ)^(k-1) * (qExpansion 1 f).coeff (p^j)) :
    coefficients f (p^(j+2)) = coefficients f p * coefficients f (p^(j+1)) -
      ξ * coefficients f (p^j) := by
  let r : ℂ := (((p : ℝ)^(-((k : ℝ)-1)/2) : ℝ) : ℂ)
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hscale : (p : ℂ)^(k-1) * r^2 = 1 := by
    dsimp [r]
    rw [← Complex.ofReal_natCast p, ← Complex.ofReal_zpow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_mul hpR.le,
      ← Real.rpow_add hpR]
    norm_num only [Int.cast_sub, Int.cast_one, Nat.cast_ofNat]
    rw [show (k : ℝ)-1 + (-((k : ℝ)-1)/2)*2 = 0 by ring, Real.rpow_zero]
  rw [coefficients_prime_pow, coefficients_prime_pow, coefficients_prime_pow, hrec]
  change (_ - ξ * (p : ℂ)^(k-1) * _) * r^(j+2) =
    ((qExpansion 1 f).coeff p * r) * (_ * r^(j+1)) - ξ * (_ * r^j)
  simp only [pow_add, pow_one]
  linear_combination -ξ * (qExpansion 1 f).coeff (p^j) * r^j * hscale

/-- The classical raw Fourier recurrences give the exact complex Euler
product of the normalized coefficients. -/
theorem coefficients_eulerProduct [NeZero N] (f : CuspForm (level N) k)
    (hone : (qExpansion 1 f).coeff 1 = 1)
    (hmul : ∀ m n, m.Coprime n → (qExpansion 1 f).coeff (m*n) =
      (qExpansion 1 f).coeff m * (qExpansion 1 f).coeff n)
    (hrec : ∀ p, p.Prime → ∀ j, (qExpansion 1 f).coeff (p^(j+2)) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff (p^(j+1)) -
        FinitenessEulerIdentification.xi N p * (p : ℂ)^(k-1) *
          (qExpansion 1 f).coeff (p^j)) :
    FinitenessOriginalInput.EulerProduct N (coefficients f) := by
  apply AsymptoticClassicalEulerProduct.eulerProduct_of_arithmetic
    (coefficients_zero f) (by simpa using hone) (coefficients_isBigO f)
    (coefficients_multiplicative f hmul)
  intro p hp j
  exact coefficients_prime_recurrence f p hp.pos j _ (hrec p hp j)

#print axioms coefficients_multiplicative
#print axioms coefficients_prime_pow
#print axioms coefficients_prime_recurrence
#print axioms coefficients_eulerProduct

end AsymptoticClassicalLSeries
