module

public import AsymptoticClassicalEulerNormalizationV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalLSeries

open UpperHalfPlane Complex AsymptoticClassicalCusp

variable {N : ℕ} {k : ℤ}

/-- The raw newform bad-prime squares have precisely the normalized
values required by E(N,k). -/
theorem coefficients_badPrimeConditions (f : CuspForm (level N) k)
    (hbad : ∀ p, p.Prime → p ∣ N →
      (qExpansion 1 f).coeff p ^ 2 = if p^2 ∣ N then 0 else (p : ℂ)^(k-2)) :
    FinitenessOriginalInput.BadPrimeConditions N (coefficients f) := by
  intro p hp hpN
  rw [coefficients, mul_pow, hbad p hp hpN]
  by_cases hpp : p^2 ∣ N
  · simp [hpp]
  rw [ite_eq_right hpp, ite_eq_right hpp]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  rw [← Complex.ofReal_natCast p, ← Complex.ofReal_zpow, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, ← Complex.ofReal_inv]
  apply congrArg Complex.ofReal
  rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_mul hpR.le,
    ← Real.rpow_add hpR]
  norm_num only [Int.cast_sub, Int.cast_ofNat, Nat.cast_ofNat]
  rw [show (k : ℝ)-2 + (-((k : ℝ)-1)/2)*2 = -1 by ring, Real.rpow_neg_one]

/-- Every part of EulerData follows from the classical raw Fourier
relations; the polynomial growth is already proved for actual cusp forms. -/
theorem coefficients_eulerData [NeZero N] (f : CuspForm (level N) k)
    (hone : (qExpansion 1 f).coeff 1 = 1)
    (hmul : ∀ m n, m.Coprime n → (qExpansion 1 f).coeff (m*n) =
      (qExpansion 1 f).coeff m * (qExpansion 1 f).coeff n)
    (hrec : ∀ p, p.Prime → ∀ j, (qExpansion 1 f).coeff (p^(j+2)) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff (p^(j+1)) -
        FinitenessEulerIdentification.xi N p * (p : ℂ)^(k-1) *
          (qExpansion 1 f).coeff (p^j))
    (hbad : ∀ p, p.Prime → p ∣ N →
      (qExpansion 1 f).coeff p ^ 2 = if p^2 ∣ N then 0 else (p : ℂ)^(k-2)) :
    FinitenessOriginalInput.EulerData N (coefficients f) where
  zero := coefficients_zero f
  growth := coefficients_growth f
  euler := coefficients_eulerProduct f hone hmul hrec
  bad := coefficients_badPrimeConditions f hbad

#print axioms coefficients_badPrimeConditions
#print axioms coefficients_eulerData

end AsymptoticClassicalLSeries
