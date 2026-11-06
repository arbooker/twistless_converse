module

public import AsymptoticClassicalHeckeFrickeV1
public import AsymptoticClassicalLocalFrickeV1
public import AsymptoticClassicalBadHeckeNewV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace AsymptoticClassicalCusp
open UpperHalfPlane

/-- Every actual prime Hecke operator commutes with normalized global Fricke
on the total newspace, including both kinds of bad prime. -/
theorem primeHecke_fricke_new (N : ℕ) [NeZero N] (hN : 0 < N)
    (k : ℕ) (hk : Even k) (f : CuspForm (level N) (k : ℤ))
    (hf : f ∈ newSpace N hN (k : ℤ)) (p : ℕ) (hp : p.Prime) :
    primeHecke N p hp (k : ℤ) (frickeOperator N hN (k : ℤ) f) =
      frickeOperator N hN (k : ℤ) (primeHecke N p hp (k : ℤ) f) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hpN : p ∣ N
  · obtain ⟨M, rfl⟩ := hpN
    have hM : 0 < M := by nlinarith
    let : NeZero M := ⟨hM.ne'⟩
    have hj := frickeOperator_mem_newSpace (p*M) hN (k : ℤ) f hf
    simp only [primeHecke, Nat.dvd_mul_right p M, ite_true]
    by_cases hpM : p ∣ M
    · rw [upperTrace_repeated_new_zero M p hp hpM (k : ℤ) _ hj,
        upperTrace_repeated_new_zero M p hp hpM (k : ℤ) f hf, map_zero]
    · have hc : p.Coprime M := hp.coprime_iff_not_dvd.mpr hpM
      have hAB : (p : ℤ)*Nat.gcdA p M+(M : ℤ)*Nat.gcdB p M=1 := by
        have hh := Nat.gcd_eq_gcd_ab p M
        rw [hc.gcd_eq_one, Nat.cast_one] at hh
        exact hh.symm
      rw [upperTrace_simple_new_eq_neg_local M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hAB
          (k : ℤ) _ hj,
        upperTrace_simple_new_eq_neg_local M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hAB
          (k : ℤ) f hf, map_neg]
      exact congrArg Neg.neg (localAtkin_fricke_commute M p hM hp.pos
        (Nat.gcdA p M) (Nat.gcdB p M) hAB (k : ℤ) f)
  · simp only [primeHecke, ite_eq_right hpN]
    exact dilationTrace_prime_fricke_commute N p hN hpN k hk f

#print axioms primeHecke_fricke_new
end AsymptoticClassicalCusp
