module

public import AsymptoticClassicalPrimeFrickeV1
public import AsymptoticClassicalEigenPrimeSolutionV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace AsymptoticClassicalCusp
open UpperHalfPlane AsymptoticClassicalEigenbasis AsymptoticClassicalLSeries

/-- Multiplicity one forces a normalized new prime eigenform to have a
normalized global Fricke sign. -/
theorem new_prime_eigen_fricke_sign (N k : ℕ) [NeZero N] (hN : 0 < N) (hk : Even k)
    (f : CuspForm (level N) (k : ℤ)) (hf : f ∈ newSpace N hN (k : ℤ))
    (hone : cuspCoefficient N (k : ℤ) 1 f = 1) (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes, primeHecke N p.val p.property (k : ℤ) f = e p • f) :
    ∃ root : ℂ, (root=1 ∨ root= -1) ∧ frickeOperator N hN (k : ℤ) f = root • f := by
  let J := frickeOperator N hN (k : ℤ)
  have hj (p : Nat.Primes) : primeHecke N p.val p.property (k : ℤ) (J f) = e p • J f := by
    rw [primeHecke_fricke_new N hN k hk f hf p.val p.property, heigen, map_smul]
  have hp := joint_vectors_proportional_of_kernel
    (fun p : Nat.Primes => primeHecke N p.val p.property (k : ℤ)) (cuspCoefficient N (k : ℤ) 1)
    (prime_eigen_first_kernel N (k : ℤ)) heigen hj
  rw [hone, one_smul] at hp
  have he : J f = cuspCoefficient N (k : ℤ) 1 (J f) • f := hp.symm
  refine ⟨cuspCoefficient N (k : ℤ) 1 (J f), ?_, he⟩
  apply sq_eq_one_iff.mp
  have hh := congrArg (fun v => cuspCoefficient N (k : ℤ) 1 (J v)) he
  rw [show J (J f) = f from frickeOperator_involutive N hN k hk f,
    map_smul, map_smul, hone] at hh
  simpa only [smul_eq_mul, pow_two] using hh.symm

/-- Every normalized common prime-Hecke eigenform in the actual newspace
satisfies the complete complex E(N,k) definition. -/
theorem new_prime_eigen_isSolution (N k : ℕ) [NeZero N] (hN : 0 < N)
    (hk : 0 < k) (heven : Even k) (f : CuspForm (level N) (k : ℤ))
    (hf : f ∈ newSpace N hN (k : ℤ)) (hone : (qExpansion 1 f).coeff 1 = 1)
    (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes, primeHecke N p.val p.property (k : ℤ) f = e p • f) :
    FinitenessOriginalInput.IsSolution N k (coefficients f) := by
  obtain ⟨root, hroot, hfr⟩ := new_prime_eigen_fricke_sign N k hN heven f hf hone e heigen
  exact prime_eigen_isSolution N k hk heven f hone e heigen
    (primeHecke_bad_square N hN (k : ℤ) f hf) root hroot hfr

#print axioms new_prime_eigen_fricke_sign
#print axioms new_prime_eigen_isSolution
end AsymptoticClassicalCusp
