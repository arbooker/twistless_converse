module

public import AsymptoticClassicalHeckeCoefficientAlgebraV1
public import AsymptoticClassicalDegeneracyRangeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalHeckeCoefficients

theorem down_hecke (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q)
    (a : ℂ) (c : ℕ → ℂ) (n : ℕ) :
    down q (hecke p a c) n = hecke p a (down q c) n := by
  change down q (fun m => c (p * m) + a * down p c m) n =
    down q c (p * n) + a * down p (down q c) n
  rw [down_add, down_mul, down_up q p hpq.symm, down_down q p hq hp]

#print axioms down_hecke

end AsymptoticClassicalHeckeCoefficients

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

variable (M q p : ℕ) [NeZero M] [NeZero (q * M)] [Fact p.Prime]
variable (hq : 0 < q) (hpN : ¬ p ∣ q * M) (k : ℤ)

/-- Restriction to a larger level leaves Fourier coefficients unchanged. -/
theorem cuspCoefficient_restrict (N M : ℕ) (hMN : M ∣ N) (k : ℤ) (n : ℕ)
    (f : CuspForm (level M) k) :
    cuspCoefficient N k n (restrict k (level_antitone hMN) f) = cuspCoefficient M k n f := rfl

/-- The literal degeneracy coefficient formula in the coefficient-functional API. -/
theorem cuspCoefficient_degeneracy (M q : ℕ) [NeZero M] (hq : 0 < q) (k : ℤ)
    (n : ℕ) (f : CuspForm (level M) k) :
    cuspCoefficient (q * M) k n (degeneracy M q hq k f) =
      if q ∣ n then cuspCoefficient M k (n / q) f else 0 := coeff_degeneracy M q hq k f n

include hpN in
/-- The good-prime operator commutes with inclusion from every lower level. -/
theorem dilationTrace_restrict (f : CuspForm (level M) k) :
    dilationTrace (q * M) p (Fact.out : p.Prime).pos k
      (restrict k (level_antitone (dvd_mul_left M q)) f) =
    restrict k (level_antitone (dvd_mul_left M q))
      (dilationTrace M p (Fact.out : p.Prime).pos k f) := by
  have hpM : ¬ p ∣ M := fun h => hpN (dvd_mul_of_dvd_right h q)
  apply sub_eq_zero.mp
  apply cuspCoefficient_separates (q * M) k
  intro n
  rw [map_sub]
  apply sub_eq_zero.mpr
  rw [cuspCoefficient_restrict (q * M) M (dvd_mul_left M q) k n,
    coeff_dilationTrace_prime (q * M) p hpN,
    coeff_dilationTrace_prime M p hpM]
  rfl

include hpN in
/-- At distinct primes, Hecke action commutes with literal oldform dilation. -/
theorem dilationTrace_degeneracy (f : CuspForm (level M) k) :
    dilationTrace (q * M) p (Fact.out : p.Prime).pos k (degeneracy M q hq k f) =
      degeneracy M q hq k (dilationTrace M p (Fact.out : p.Prime).pos k f) := by
  have hpM : ¬ p ∣ M := fun h => hpN (dvd_mul_of_dvd_right h q)
  have hpq : p.Coprime q := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (fun h => hpN (dvd_mul_of_dvd_left h M))
  apply sub_eq_zero.mp
  apply cuspCoefficient_separates (q * M) k
  intro n
  rw [map_sub]
  apply sub_eq_zero.mpr
  rw [coeff_dilationTrace_prime (q * M) p hpN]
  simp_rw [cuspCoefficient_degeneracy, coeff_dilationTrace_prime M p hpM]
  have hh := AsymptoticClassicalHeckeCoefficients.down_hecke p q
    (Fact.out : p.Prime).pos hq hpq ((p : ℂ) ^ (k - 1))
    (fun m => cuspCoefficient M k m f) n
  simpa only [AsymptoticClassicalHeckeCoefficients.down,
    AsymptoticClassicalHeckeCoefficients.hecke] using hh.symm

#print axioms cuspCoefficient_restrict
#print axioms cuspCoefficient_degeneracy
#print axioms dilationTrace_restrict
#print axioms dilationTrace_degeneracy

end AsymptoticClassicalCusp
