module

public import AsymptoticClassicalBadHeckeSimpleV1
public import AsymptoticClassicalPrimeHeckeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
namespace AsymptoticClassicalCusp
open UpperHalfPlane

/-- At a simple bad prime, U_p is minus the actual local Atkin slash
operator on the full newspace. -/
theorem upperTrace_simple_new_eq_neg_local (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (hpM : ¬ p ∣ M) (A B : ℤ)
    (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (k : ℤ)
    (f : CuspForm (level (p * M)) k)
    (hf : f ∈ newSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) k) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
    upperTrace (p * M) p (Fact.out : p.Prime).pos k f =
      -localAtkinOperator M p (Fact.out : p.Prime).pos A B hAB k f :=
  upperTrace_simple_eq_neg_local M p hM hpM A B hAB k f (new_factor_traces M p hM k f hf).2

/-- The precise bad-prime square relation holds on the actual total newspace. -/
theorem primeHecke_bad_square (N : ℕ) [NeZero N] (hN : 0 < N) (k : ℤ)
    (f : CuspForm (level N) k) (hf : f ∈ newSpace N hN k)
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) :
    primeHecke N p hp k (primeHecke N p hp k f) =
      (if p^2 ∣ N then (0 : ℂ) else (p : ℂ)^(k-2)) • f := by
  obtain ⟨M, rfl⟩ := hpN
  have hM : 0 < M := by nlinarith
  let : NeZero M := ⟨hM.ne'⟩
  let : Fact p.Prime := ⟨hp⟩
  simp only [primeHecke, Nat.dvd_mul_right p M, ite_true]
  by_cases hpM : p ∣ M
  · have hsq : p^2 ∣ p * M := by
      rw [pow_two]
      exact mul_dvd_mul_left p hpM
    rw [ite_eq_left hsq, zero_smul, upperTrace_repeated_new_zero M p hp hpM k f hf, map_zero]
  · have hsq : ¬ p^2 ∣ p * M := by
      rw [pow_two, mul_dvd_mul_iff_left hp.ne_zero]
      exact hpM
    rw [ite_eq_right hsq]
    have hc : p.Coprime M := hp.coprime_iff_not_dvd.mpr hpM
    have hAB : (p : ℤ) * Nat.gcdA p M + (M : ℤ) * Nat.gcdB p M = 1 := by
      have hh := Nat.gcd_eq_gcd_ab p M
      rw [hc.gcd_eq_one, Nat.cast_one] at hh
      exact hh.symm
    exact upperTrace_simple_new_square M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hAB k f hf

#print axioms upperTrace_simple_new_eq_neg_local
#print axioms primeHecke_bad_square
end AsymptoticClassicalCusp
