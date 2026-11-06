module

public import AsymptoticClassicalHeckeCoefficientV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

/-- The coefficient law is independent of auxiliary Bezout choices. -/
theorem coeff_dilationTrace_prime (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hpN : ¬ p ∣ N) (k : ℤ) (f : CuspForm (level N) k) (n : ℕ) :
    cuspCoefficient N k n (dilationTrace N p (Fact.out : p.Prime).pos k f) =
      cuspCoefficient N k (p * n) f + (p : ℂ) ^ (k - 1) *
        if p ∣ n then cuspCoefficient N k (n / p) f else 0 := by
  have hc : p.Coprime N := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN
  have hAB : (p : ℤ) * Nat.gcdA p N + (N : ℤ) * Nat.gcdB p N = 1 := by
    have hh := Nat.gcd_eq_gcd_ab p N
    rw [hc.gcd_eq_one, Nat.cast_one] at hh
    exact hh.symm
  exact coeff_dilationTrace N p (Nat.pos_of_ne_zero (NeZero.ne N)) hpN
    (Nat.gcdA p N) (Nat.gcdB p N) hAB k f n

/-- The first coefficient of T_p f is the p-th coefficient of f. -/
theorem first_dilationTrace_prime (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hpN : ¬ p ∣ N) (k : ℤ) (f : CuspForm (level N) k) :
    cuspCoefficient N k 1 (dilationTrace N p (Fact.out : p.Prime).pos k f) =
      cuspCoefficient N k p f := by
  rw [coeff_dilationTrace_prime N p hpN]
  simp [(Fact.out : p.Prime).not_dvd_one]

#print axioms coeff_dilationTrace_prime
#print axioms first_dilationTrace_prime

end AsymptoticClassicalCusp
