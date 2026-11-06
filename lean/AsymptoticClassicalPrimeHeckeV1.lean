module

public import AsymptoticClassicalBadHeckeV1
public import AsymptoticClassicalHeckeCoefficientAlgebraV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

/-- The usual prime Hecke operator, with the U_p correspondence at bad primes. -/
def primeHecke (N p : ℕ) [NeZero N] (hp : p.Prime) (k : ℤ) :
    CuspForm (level N) k →ₗ[ℂ] CuspForm (level N) k :=
  if p ∣ N then upperTrace N p hp.pos k else dilationTrace N p hp.pos k

/-- The local quadratic coefficient is zero at bad primes. -/
def primeHeckeFactor (N p : ℕ) (k : ℤ) : ℂ := if p ∣ N then 0 else (p : ℂ) ^ (k - 1)

theorem coeff_primeHecke (N p : ℕ) [NeZero N] (hp : p.Prime) (k : ℤ)
    (f : CuspForm (level N) k) (n : ℕ) :
    cuspCoefficient N k n (primeHecke N p hp k f) =
      cuspCoefficient N k (p * n) f + primeHeckeFactor N p k *
        (if p ∣ n then cuspCoefficient N k (n / p) f else 0) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hpN : p ∣ N
  · simp only [primeHecke, primeHeckeFactor, hpN, ite_true, zero_mul, add_zero]
    exact coeff_upperTrace_bad N p hp hpN k f n
  · simp only [primeHecke, primeHeckeFactor, hpN, ite_false]
    exact coeff_dilationTrace_prime N p hpN k f n

theorem first_primeHecke (N p : ℕ) [NeZero N] (hp : p.Prime) (k : ℤ)
    (f : CuspForm (level N) k) :
    cuspCoefficient N k 1 (primeHecke N p hp k f) = cuspCoefficient N k p f := by
  rw [coeff_primeHecke]
  simp [hp.not_dvd_one]

/-- The actual good and bad prime operators all commute at distinct primes. -/
theorem primeHecke_commute (N p q : ℕ) [NeZero N] (hp : p.Prime) (hq : q.Prime)
    (hpq : p.Coprime q) (k : ℤ) :
    Function.Commute (primeHecke N p hp k) (primeHecke N q hq k) := by
  intro f
  apply sub_eq_zero.mp
  apply cuspCoefficient_separates N k
  intro n
  rw [map_sub]
  apply sub_eq_zero.mpr
  simp_rw [coeff_primeHecke N p hp, coeff_primeHecke N q hq, coeff_primeHecke N p hp]
  have hh := congrFun (AsymptoticClassicalHeckeCoefficients.hecke_commute p q hp.pos hq.pos hpq
    (primeHeckeFactor N p k) (primeHeckeFactor N q k)
    (fun m => cuspCoefficient N k m f)) n
  simpa only [AsymptoticClassicalHeckeCoefficients.hecke,
    AsymptoticClassicalHeckeCoefficients.down] using hh

#print axioms coeff_primeHecke
#print axioms first_primeHecke
#print axioms primeHecke_commute
end AsymptoticClassicalCusp
