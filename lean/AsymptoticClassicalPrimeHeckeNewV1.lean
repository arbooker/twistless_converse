module

public import AsymptoticClassicalLocalAtkinNewV1
public import AsymptoticClassicalBadHeckeSimpleV1
public import AsymptoticClassicalBadHeckeRepeatedV1
public import AsymptoticClassicalPrimeHeckeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalPetersson
open scoped ModularForm InnerProduct

/-- Every actual prime correspondence preserves the full classical newspace. -/
theorem primeHecke_mem_newSpace (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) (hp : p.Prime)
    (k : ℤ) (f : CuspForm (level N) k) (hf : f ∈ newSpace N hN k) :
    primeHecke N p hp k f ∈ newSpace N hN k := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hpN : p ∣ N
  · simp only [primeHecke, hpN, ite_true]
    obtain ⟨M, rfl⟩ := hpN
    have hM : 0 < M := Nat.pos_of_mul_pos_left hN
    let : NeZero M := ⟨hM.ne'⟩
    by_cases hpM : p ∣ M
    · rw [upperTrace_repeated_new_zero M p hp hpM k f hf]
      exact (newSpace (p * M) hN k).zero_mem
    · have hc : p.Coprime M := hp.coprime_iff_not_dvd.mpr hpM
      have hAB : (p : ℤ) * Nat.gcdA p M + (M : ℤ) * Nat.gcdB p M = 1 := by
        have hh := Nat.gcd_eq_gcd_ab p M
        rw [hc.gcd_eq_one, Nat.cast_one] at hh
        exact hh.symm
      rw [upperTrace_simple_eq_neg_local M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hAB k f
        (new_factor_traces M p hM k f hf).2]
      exact (newSpace (p * M) hN k).neg_mem
        (localAtkin_mem_newSpace M p hM (Nat.gcdA p M) (Nat.gcdB p M) hAB k f hf)
  · simp only [primeHecke, hpN, ite_false]
    exact dilationTrace_mem_newSpace N hN p hpN k f hf

/-- All prime correspondences are symmetric when restricted to genuine new forms. -/
theorem primeHecke_inner_new (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) (hp : p.Prime)
    (k : ℤ) (f : CuspForm (level N) k) (hf : f ∈ newSpace N hN k)
    (g : CuspForm (level N) k) (hg : g ∈ newSpace N hN k) :
    inner ℂ (primeHecke N p hp k f) g = inner ℂ f (primeHecke N p hp k g) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hpN : p ∣ N
  · simp only [primeHecke, hpN, ite_true]
    obtain ⟨M, rfl⟩ := hpN
    have hM : 0 < M := Nat.pos_of_mul_pos_left hN
    let : NeZero M := ⟨hM.ne'⟩
    by_cases hpM : p ∣ M
    · rw [upperTrace_repeated_new_zero M p hp hpM k f hf,
        upperTrace_repeated_new_zero M p hp hpM k g hg, inner_zero_left, inner_zero_right]
    · have hc : p.Coprime M := hp.coprime_iff_not_dvd.mpr hpM
      have hAB : (p : ℤ) * Nat.gcdA p M + (M : ℤ) * Nat.gcdB p M = 1 := by
        have hh := Nat.gcd_eq_gcd_ab p M
        rw [hc.gcd_eq_one, Nat.cast_one] at hh
        exact hh.symm
      rw [upperTrace_simple_eq_neg_local M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hAB k f
        (new_factor_traces M p hM k f hf).2,
        upperTrace_simple_eq_neg_local M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hAB k g
        (new_factor_traces M p hM k g hg).2, inner_neg_left, inner_neg_right]
      rw [localAtkinOperator_isSymmetric M p hp.pos (Nat.gcdA p M) (Nat.gcdB p M) hAB k]
  · simp only [primeHecke, hpN, ite_false]
    have hc : p.Coprime N := hp.coprime_iff_not_dvd.mpr hpN
    have hAB : (p : ℤ) * Nat.gcdA p N + (N : ℤ) * Nat.gcdB p N = 1 := by
      have hh := Nat.gcd_eq_gcd_ab p N
      rw [hc.gcd_eq_one, Nat.cast_one] at hh
      exact hh.symm
    exact dilationTrace_isSymmetric N p hp.pos k (Nat.gcdA p N) (Nat.gcdB p N) hAB f g

#print axioms primeHecke_mem_newSpace
#print axioms primeHecke_inner_new

end AsymptoticClassicalCusp
