module

public import AsymptoticClassicalPrimeHeckeNewV1
public import AsymptoticClassicalEigenCuspPrimeV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace AsymptoticClassicalCusp
open UpperHalfPlane AsymptoticClassicalEigenbasis
open scoped InnerProduct

/-- The actual good and bad prime Hecke endomorphisms on the total newspace. -/
def newPrimeHecke (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) (hp : p.Prime) (k : ℤ) :
    newSpace N hN k →ₗ[ℂ] newSpace N hN k :=
  (primeHecke N p hp k).restrict (fun f hf => primeHecke_mem_newSpace N hN p hp k f hf)

@[simp] theorem newPrimeHecke_val (N : ℕ) [NeZero N] (hN : 0 < N)
    (p : ℕ) (hp : p.Prime) (k : ℤ) (f : newSpace N hN k) :
    (newPrimeHecke N hN p hp k f).val = primeHecke N p hp k f.val := rfl

theorem newPrimeHecke_isSymmetric (N : ℕ) [NeZero N] (hN : 0 < N)
    (p : ℕ) (hp : p.Prime) (k : ℤ) : (newPrimeHecke N hN p hp k).IsSymmetric := by
  intro f g
  exact primeHecke_inner_new N hN p hp k f.val f.property g.val g.property

theorem newPrimeHecke_pairwise_commute (N : ℕ) [NeZero N] (hN : 0 < N) (k : ℤ) :
    Pairwise (fun p q : Nat.Primes => Commute (newPrimeHecke N hN p.val p.property k)
      (newPrimeHecke N hN q.val q.property k)) := by
  intro p q hpq
  have hc : p.val.Coprime q.val := p.property.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hpq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.property q.property).mp hd)))
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact primeHecke_commute N p.val q.val p.property q.property hc k f.val

/-- The total newspace has a full family of distinct, first-coefficient-one
common eigenforms for all genuine prime Hecke operators. -/
theorem exists_normalized_new_prime_family (N : ℕ) [NeZero N] (hN : 0 < N) (k : ℤ) :
    ∃ f : Fin (Module.finrank ℂ (newSpace N hN k)) → newSpace N hN k,
      Function.Injective f ∧ (∀ j, (qExpansion 1 (f j).val).coeff 1 = 1) ∧
      ∀ j, ∃ e : Nat.Primes → ℂ, ∀ p : Nat.Primes,
        primeHecke N p.val p.property k (f j).val = e p • (f j).val := by
  obtain ⟨f, hf, hone, he⟩ := exists_normalized_joint_family_of_kernel
    (fun p : Nat.Primes => newPrimeHecke N hN p.val p.property k)
    (fun p => newPrimeHecke_isSymmetric N hN p.val p.property k)
    (newPrimeHecke_pairwise_commute N hN k) (newCoefficient N hN k 1)
    (by
      intro v e he hv
      apply Subtype.ext
      apply prime_eigen_first_kernel N k v.val e
      · intro p
        exact congrArg Subtype.val (he p)
      · exact hv)
  refine ⟨f, hf, hone, ?_⟩
  intro j
  obtain ⟨e, he⟩ := he j
  exact ⟨e, fun p => congrArg Subtype.val (he p)⟩

#print axioms newPrimeHecke_isSymmetric
#print axioms newPrimeHecke_pairwise_commute
#print axioms exists_normalized_new_prime_family
end AsymptoticClassicalCusp
