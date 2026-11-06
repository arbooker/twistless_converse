module

public import AsymptoticClassicalHeckeCoefficientAlgebraV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

/-- Coprime good-prime Hecke operators commute on the actual classical
 cusp space; equality is established by all Fourier coefficients. -/
theorem dilationTrace_commute_of_coprime (N p q : ℕ) [NeZero N]
    [Fact p.Prime] [Fact q.Prime] (hpN : ¬ p ∣ N) (hqN : ¬ q ∣ N)
    (hpq : p.Coprime q) (k : ℤ) :
    Function.Commute (dilationTrace N p (Fact.out : p.Prime).pos k)
      (dilationTrace N q (Fact.out : q.Prime).pos k) := by
  intro f
  apply sub_eq_zero.mp
  apply cuspCoefficient_separates N k
  intro n
  rw [map_sub]
  apply sub_eq_zero.mpr
  simp_rw [coeff_dilationTrace_prime N p hpN, coeff_dilationTrace_prime N q hqN,
    coeff_dilationTrace_prime N p hpN]
  have hh := congrFun (AsymptoticClassicalHeckeCoefficients.hecke_commute p q
    (Fact.out : p.Prime).pos (Fact.out : q.Prime).pos hpq
    ((p : ℂ) ^ (k - 1)) ((q : ℂ) ^ (k - 1))
    (fun m => cuspCoefficient N k m f)) n
  simpa only [AsymptoticClassicalHeckeCoefficients.hecke,
    AsymptoticClassicalHeckeCoefficients.down] using hh

#print axioms dilationTrace_commute_of_coprime

end AsymptoticClassicalCusp
