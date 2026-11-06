module

public import AsymptoticClassicalEigenCuspPrimeV1
public import AsymptoticClassicalFrickeNewV1
public import AsymptoticClassicalEulerSolutionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalLSeries

/-- On a normalized prime eigenform, the bad-prime operator square
identity becomes the required raw Fourier coefficient square. -/
theorem prime_eigen_bad_square (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm (level N) k) (hone : (qExpansion 1 f).coeff 1 = 1)
    (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes, primeHecke N p.val p.property k f = e p • f)
    (p : ℕ) (hp : p.Prime)
    (hsquare : primeHecke N p hp k (primeHecke N p hp k f) =
      (if p^2 ∣ N then (0 : ℂ) else (p : ℂ)^(k-2)) • f) :
    (qExpansion 1 f).coeff p ^ 2 = if p^2 ∣ N then 0 else (p : ℂ)^(k-2) := by
  have he := heigen (⟨p,hp⟩ : Nat.Primes)
  have h := congrArg (cuspCoefficient N k 1) hsquare
  rw [he, map_smul, he, map_smul, map_smul, map_smul] at h
  change e ⟨p,hp⟩ • (e ⟨p,hp⟩ • (qExpansion 1 f).coeff 1) =
    (if p^2 ∣ N then (0 : ℂ) else (p : ℂ)^(k-2)) • (qExpansion 1 f).coeff 1 at h
  rw [hone, prime_eigenvalue N k f hone e heigen (⟨p,hp⟩ : Nat.Primes)] at h
  simpa only [smul_eq_mul, mul_one, pow_two] using h

/-- Actual prime-Hecke and normalized Fricke eigenrelations, together
with the bad-prime operator squares, produce a literal complex E(N,k)
solution. All coefficient arithmetic and analytic requirements are proved. -/
theorem prime_eigen_isSolution (N k : ℕ) [NeZero N] (hk : 0 < k) (heven : Even k)
    (f : CuspForm (level N) (k : ℤ)) (hone : (qExpansion 1 f).coeff 1 = 1)
    (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes, primeHecke N p.val p.property (k : ℤ) f = e p • f)
    (hsquare : ∀ p, ∀ hp : p.Prime, p ∣ N →
      primeHecke N p hp (k : ℤ) (primeHecke N p hp (k : ℤ) f) =
        (if p^2 ∣ N then (0 : ℂ) else (p : ℂ)^((k : ℤ)-2)) • f)
    (root : ℂ) (hroot : root = 1 ∨ root = -1)
    (hfr : frickeOperator N (Nat.pos_of_ne_zero (NeZero.ne N)) (k : ℤ) f = root • f) :
    FinitenessOriginalInput.IsSolution N k (coefficients f) := by
  apply coefficients_isSolution N k hk heven f hone
    (prime_eigen_multiplicative N (k : ℤ) f hone e heigen)
    (prime_eigen_prime_power N (k : ℤ) f hone e heigen)
    (fun p hp hpN => prime_eigen_bad_square N (k : ℤ) f hone e heigen p hp (hsquare p hp hpN))
    root hroot
  have h := congrArg (fun u : CuspForm (level N) (k : ℤ) => (u : ℍ → ℂ)) hfr
  simpa only [frickeOperator_coe, FunLike.coe_smul] using h

#print axioms prime_eigen_bad_square
#print axioms prime_eigen_isSolution

end AsymptoticClassicalCusp
