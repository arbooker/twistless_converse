module

public import AsymptoticClassicalMultiplicityKernelsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

/-- The actual trace-new conditions imposed only at a chosen set of primes. -/
def partialNewSpace (N : ℕ) (hN : 0 < N) (k : ℤ) (S : Set ℕ) :
    Submodule ℂ (CuspForm (level N) k) :=
  ⨅ p : {p : ℕ // p.Prime ∧ p ∣ N}, ⨅ (_ : p.val ∈ S), primeTraceKernel N hN k p

theorem mem_partialNewSpace (N : ℕ) (hN : 0 < N) (k : ℤ) (S : Set ℕ)
    (f : CuspForm (level N) k) :
    f ∈ partialNewSpace N hN k S ↔
      ∀ p : {p : ℕ // p.Prime ∧ p ∣ N}, p.val ∈ S → f ∈ primeTraceKernel N hN k p := by
  simp only [partialNewSpace, Submodule.mem_iInf]

theorem partialNewSpace_univ (N : ℕ) (hN : 0 < N) (k : ℤ) :
    partialNewSpace N hN k Set.univ = newSpace N hN k := by
  ext f
  simp only [mem_partialNewSpace, mem_newSpace, Set.mem_univ, true_implies]

theorem partialNewSpace_empty (N : ℕ) (hN : 0 < N) (k : ℤ) :
    partialNewSpace N hN k ∅ = ⊤ := by
  ext f
  simp only [mem_partialNewSpace, Set.mem_empty_iff_false, false_implies,
    implies_true, Submodule.mem_top]

/-- Ordinary inclusion across a coprime factor preserves the literal
 prime trace kernel, including its original Fricke target. -/
theorem restrict_mem_cross_primeTraceKernel (M p q : ℕ) [NeZero M] [NeZero p]
    (hM : 0 < M) (hp : 0 < p) (hq : q.Prime) (hqM : q ∣ M)
    (hc : p.Coprime q) (k : ℤ) (f : CuspForm (level M) k)
    (hf : f ∈ primeTraceKernel M hM k ⟨q, hq, hqM⟩) :
    restrict k (level_antitone (Nat.dvd_mul_left M p)) f ∈
      primeTraceKernel (p * M) (Nat.mul_pos hp hM) k
        ⟨q, hq, dvd_mul_of_dvd_right hqM p⟩ := by
  let : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨L, rfl⟩ := hqM
  have hL : 0 < L := by
    by_contra he
    have hL0 : L = 0 := by omega
    simp [hL0] at hM
  let : NeZero L := ⟨hL.ne'⟩
  rw [primeTraceKernel_eq_twoTraceKernel] at hf ⊢
  have hs : f ∈ twoTraceKernel (q * L) L q hq.pos k := by
    simpa only [Nat.mul_div_cancel_left L hq.pos] using hf
  have ht := restrict_mem_cross_twoTraceKernel L p q hL hp hq hc k f hs
  have hd : p * (q * L) / q = p * L := by
    rw [Nat.mul_left_comm p q L, Nat.mul_div_cancel_left (p * L) hq.pos]
  simpa only [hd] using ht

/-- Fricke preserves every partial intersection of prime-new conditions. -/
theorem frickeOperator_mem_partialNewSpace (N : ℕ) (hN : 0 < N) (k : ℤ) (S : Set ℕ)
    (f : CuspForm (level N) k) (hf : f ∈ partialNewSpace N hN k S) :
    frickeOperator N hN k f ∈ partialNewSpace N hN k S := by
  rw [mem_partialNewSpace] at hf ⊢
  exact fun p hp => frickeOperator_mem_primeTraceKernel N hN k p f (hf p hp)

/-- Adding a new prime factor preserves the new conditions already imposed
 at all the other primes. -/
theorem restrict_mem_partialNewSpace (M p : ℕ) [NeZero M] (hM : 0 < M) (hp : p.Prime)
    (k : ℤ) (S : Set ℕ) (hpS : p ∉ S) (f : CuspForm (level M) k)
    (hf : f ∈ partialNewSpace M hM k S) :
    restrict k (level_antitone (Nat.dvd_mul_left M p)) f ∈
      partialNewSpace (p * M) (Nat.mul_pos hp.pos hM) k S := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [mem_partialNewSpace] at hf ⊢
  intro q hqS
  have hne : q.val ≠ p := fun he => hpS (he ▸ hqS)
  have hn : ¬q.val ∣ p := fun hd => hne ((Nat.prime_dvd_prime_iff_eq q.property.1 hp).mp hd)
  have hqM : q.val ∣ M := (q.property.1.dvd_mul.mp q.property.2).resolve_left hn
  have hc : p.Coprime q.val := (q.property.1.coprime_iff_not_dvd.mpr hn).symm
  exact restrict_mem_cross_primeTraceKernel M p q.val hM hp.pos q.property.1 hqM hc k f
    (hf ⟨q.val, q.property.1, hqM⟩ hqS)

#print axioms mem_partialNewSpace
#print axioms partialNewSpace_univ
#print axioms partialNewSpace_empty
#print axioms restrict_mem_cross_primeTraceKernel
#print axioms frickeOperator_mem_partialNewSpace
#print axioms restrict_mem_partialNewSpace

end AsymptoticClassicalCusp
