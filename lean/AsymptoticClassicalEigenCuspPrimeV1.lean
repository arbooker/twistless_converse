module

public import AsymptoticClassicalPrimeHeckeV1
public import AsymptoticClassicalEigenPrimeBasisV1
public import AsymptoticClassicalEigenPrimeArithmeticV1
public import FinitenessEulerIdentificationV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalEigenbasis

variable (N : ℕ) [NeZero N] (k : ℤ)

/-- Every actual common prime-Hecke eigenvector has nonzero first
coefficient unless it is the zero cusp form. -/
theorem prime_eigen_first_kernel (f : CuspForm (level N) k) (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes, primeHecke N p.val p.property k f = e p • f)
    (hfirst : cuspCoefficient N k 1 f = 0) : f = 0 := by
  apply prime_joint_first_kernel
    (fun p : Nat.Primes => primeHecke N p.val p.property k)
    (cuspCoefficient N k) (fun p => primeHeckeFactor N p.val k)
    (fun v => CuspFormClass.qExpansion_coeff_zero v zero_lt_one (level_one_period N))
    (cuspCoefficient_separates N k)
    (fun p n v => coeff_primeHecke N p.val p.property k v n) heigen hfirst

/-- The exact coefficient recurrence of an actual prime-Hecke eigenform. -/
theorem prime_eigen_recurrence (f : CuspForm (level N) k) (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes, primeHecke N p.val p.property k f = e p • f)
    (p : Nat.Primes) (n : ℕ) :
    (qExpansion 1 f).coeff (p.val*n) = e p * (qExpansion 1 f).coeff n -
      primeHeckeFactor N p.val k * (if p.val ∣ n then (qExpansion 1 f).coeff (n/p.val) else 0) := by
  have h := coeff_primeHecke N p.val p.property k f n
  rw [heigen, map_smul, smul_eq_mul] at h
  exact eq_sub_iff_add_eq.mpr h.symm

/-- First-coefficient-one eigenforms have the literal prime Fourier
coefficients as their operator eigenvalues. -/
theorem prime_eigenvalue (f : CuspForm (level N) k)
    (hone : (qExpansion 1 f).coeff 1 = 1) (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes, primeHecke N p.val p.property k f = e p • f)
    (p : Nat.Primes) : e p = (qExpansion 1 f).coeff p.val :=
  prime_eigenvalue_eq_coefficient (fun n => (qExpansion 1 f).coeff n) e
    (fun p => primeHeckeFactor N p.val k) hone (prime_eigen_recurrence N k f e heigen) p

/-- Actual prime eigenrelations imply coprime multiplicativity of all
raw Fourier coefficients. -/
theorem prime_eigen_multiplicative (f : CuspForm (level N) k)
    (hone : (qExpansion 1 f).coeff 1 = 1) (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes, primeHecke N p.val p.property k f = e p • f) :
    ∀ m n, m.Coprime n → (qExpansion 1 f).coeff (m*n) =
      (qExpansion 1 f).coeff m * (qExpansion 1 f).coeff n := by
  apply multiplicative_of_prime_recurrence (fun n => (qExpansion 1 f).coeff n)
    (fun p => primeHeckeFactor N p.val k)
    (CuspFormClass.qExpansion_coeff_zero f zero_lt_one (level_one_period N)) hone
  intro p n
  rw [← prime_eigenvalue N k f hone e heigen p]
  exact prime_eigen_recurrence N k f e heigen p n

/-- The actual prime operators give the standard weight-k quadratic
recurrences, including vanishing quadratic coefficient at bad primes. -/
theorem prime_eigen_prime_power (f : CuspForm (level N) k)
    (hone : (qExpansion 1 f).coeff 1 = 1) (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes, primeHecke N p.val p.property k f = e p • f)
    (p : ℕ) (hp : p.Prime) (j : ℕ) :
    (qExpansion 1 f).coeff (p^(j+2)) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff (p^(j+1)) -
        FinitenessEulerIdentification.xi N p * (p : ℂ)^(k-1) *
          (qExpansion 1 f).coeff (p^j) := by
  have hr (q : Nat.Primes) (n : ℕ) : (qExpansion 1 f).coeff (q.val*n) =
      (qExpansion 1 f).coeff q.val * (qExpansion 1 f).coeff n -
        primeHeckeFactor N q.val k *
          (if q.val ∣ n then (qExpansion 1 f).coeff (n/q.val) else 0) := by
    rw [← prime_eigenvalue N k f hone e heigen q]
    exact prime_eigen_recurrence N k f e heigen q n
  have h := prime_power_of_prime_recurrence (fun n => (qExpansion 1 f).coeff n)
    (fun q => primeHeckeFactor N q.val k) hr (⟨p,hp⟩ : Nat.Primes) j
  simpa only [primeHeckeFactor, FinitenessEulerIdentification.xi, ite_mul, zero_mul, one_mul] using h

#print axioms prime_eigen_first_kernel
#print axioms prime_eigen_recurrence
#print axioms prime_eigenvalue
#print axioms prime_eigen_multiplicative
#print axioms prime_eigen_prime_power

end AsymptoticClassicalCusp
