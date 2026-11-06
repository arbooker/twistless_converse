module

public import QuantitativeArithmeticSmallLevelCircModularHeckeTheoryV4
public import QuantitativeArithmeticSmallLevelCircModularLSeriesTheoryV4

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane AsymptoticClassicalEigenbasis
open scoped ModularForm

variable {N k : ℕ} [NeZero N] {hN : 0<N}

/-- Actual simultaneous eigenrelations in the ambient modular space imply
the coefficient recurrence, without presupposing Hecke invariance of the subspace. -/
theorem recurrence_of_prime_eigen (F : space N hN k) (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes,
      ModularHecke.primeHecke N p.val p.property (k : ℤ) F.val = e p • F.val) :
    HasPrimeRecurrence F e (fun p => ModularHecke.primeHeckeFactor N p.val (k : ℤ)) := by
  intro p n
  have h := ModularHecke.coeff_primeHecke N p.val p.property (k : ℤ) F.val n
  rw [heigen, map_smul, smul_eq_mul] at h
  exact eq_sub_iff_add_eq.mpr h.symm

/-- The genuine common eigenline has a unique first-coefficient-one element. -/
theorem prime_eigen_normalize (F : space N hN k) (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes,
      ModularHecke.primeHecke N p.val p.property (k : ℤ) F.val = e p • F.val)
    (hne : F ≠ 0) :
    ∃! G : space N hN k, coefficient N hN k 1 G = 1 ∧
      ∀ p : Nat.Primes,
        ModularHecke.primeHecke N p.val p.property (k : ℤ) G.val = e p • G.val := by
  have hr := recurrence_of_prime_eigen F e heigen
  have hfirst : coefficient N hN k 1 F ≠ 0 := fun h => hne (hr.first_kernel h)
  let G := (coefficient N hN k 1 F)⁻¹ • F
  have hGone : coefficient N hN k 1 G = 1 := by simp [G, hfirst]
  have hGe (p : Nat.Primes) :
      ModularHecke.primeHecke N p.val p.property (k : ℤ) G.val = e p • G.val := by
    simp only [G, Submodule.coe_smul, map_smul, heigen]
    exact smul_comm _ _ _
  refine ⟨G, ⟨hGone,hGe⟩, ?_⟩
  intro H hH
  exact (recurrence_of_prime_eigen H e hH.2).unique
    (recurrence_of_prime_eigen G e hGe) (hH.1.trans hGone.symm)

theorem prime_eigen_prime_power (F : space N hN k)
    (hone : coefficient N hN k 1 F = 1) (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes,
      ModularHecke.primeHecke N p.val p.property (k : ℤ) F.val = e p • F.val)
    (p : ℕ) (hp : p.Prime) (j : ℕ) :
    (qExpansion 1 F.val).coeff (p^(j+2)) =
      (qExpansion 1 F.val).coeff p * (qExpansion 1 F.val).coeff (p^(j+1)) -
        FinitenessEulerIdentification.xi N p * (p : ℂ)^((k : ℤ)-1) *
          (qExpansion 1 F.val).coeff (p^j) := by
  have hr := recurrence_of_prime_eigen F e heigen
  have hrec (q : Nat.Primes) (n : ℕ) : coefficient N hN k (q.val*n) F =
      coefficient N hN k q.val F * coefficient N hN k n F -
        ModularHecke.primeHeckeFactor N q.val (k : ℤ) *
          (if q.val ∣ n then coefficient N hN k (n/q.val) F else 0) := by
    rw [← hr.prime_eigenvalue hone q]
    exact hr q n
  have h := prime_power_of_prime_recurrence (fun n => coefficient N hN k n F)
    (fun q => ModularHecke.primeHeckeFactor N q.val (k : ℤ)) hrec
    (⟨p,hp⟩ : Nat.Primes) j
  have hc (n : ℕ) : coefficient N hN k n F = (qExpansion 1 F.val).coeff n := rfl
  simpa only [ModularHecke.primeHeckeFactor, FinitenessEulerIdentification.xi,
    ite_mul, zero_mul, one_mul, hc] using h

/-- Full modular Hecke eigenpackets supply original Euler solutions once their
ramified square relation and actual Fricke sign are established. Multiplicativity,
the Euler recurrence, continuation, growth and finite order are all derived. -/
theorem prime_eigen_isSolution (hk : 0<k) (heven : Even k)
    (F : space N hN k) (hone : coefficient N hN k 1 F = 1)
    (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes,
      ModularHecke.primeHecke N p.val p.property (k : ℤ) F.val = e p • F.val)
    (hbad : ∀ p, p.Prime → p∣N →
      (qExpansion 1 F.val).coeff p ^ 2 = if p^2∣N then 0 else (p : ℂ)^((k : ℤ)-2))
    (eta : ℂ) (heta : eta=1 ∨ eta= -1)
    (hfr : (F.val : ℍ → ℂ) ∣[(k : ℤ)] SmallLevelNormalized.fricke N hN =
      eta • (F.val : ℍ → ℂ)) :
    FinitenessOriginalInput.IsSolution N k (ModularLSeries.coefficients F.val) := by
  exact ModularLSeries.coefficients_isSolution N k hN hk heven F.val F.property hone
    ((recurrence_of_prime_eigen F e heigen).multiplicative hone)
    (prime_eigen_prime_power F hone e heigen) hbad eta heta hfr

#print axioms recurrence_of_prime_eigen
#print axioms prime_eigen_normalize
#print axioms prime_eigen_prime_power
#print axioms prime_eigen_isSolution
end QuantitativeArithmeticSmallLevelCirc
