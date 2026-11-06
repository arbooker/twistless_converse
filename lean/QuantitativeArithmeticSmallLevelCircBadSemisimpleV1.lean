module

public import QuantitativeArithmeticSmallLevelCircAllHeckeV1
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.FieldTheory.Separable

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane AsymptoticClassicalCusp Polynomial

theorem allHecke_repeated_zero (N k : ℕ) [NeZero N] (hN : 0 < N) (hk : Even k)
    (p : Nat.Primes) (hp2 : p.val^2 ∣ N) : allHecke N k hN hk p = 0 := by
  have hpN : p.val ∣ N := (dvd_pow_self p.val (by decide : 2 ≠ 0)).trans hp2
  obtain ⟨M, rfl⟩ := hpN
  have hM : 0 < M := Nat.pos_of_mul_pos_left hN
  let : NeZero M := ⟨hM.ne'⟩
  have hpM : p.val ∣ M := by
    rwa [pow_two, mul_dvd_mul_iff_left p.property.ne_zero] at hp2
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  change ModularHecke.primeHecke (p.val * M) p.val p.property (k : ℤ) F.val = 0
  simp only [ModularHecke.primeHecke, Nat.dvd_mul_right p.val M, ite_true]
  exact ModularHecke.upperTrace_repeated_zero_of_trace M p.val p.property hpM (k : ℤ) F.val
    (factor_traces M p.val k p.property hM F.val F.property).2

theorem allHecke_bad_square (N k : ℕ) [NeZero N] (hN : 0 < N) (hk : Even k)
    (p : Nat.Primes) (hpN : p.val ∣ N) :
    allHecke N k hN hk p ^ 2 =
      (if p.val^2 ∣ N then (0 : ℂ) else (p.val : ℂ)^((k : ℤ)-2)) • 1 := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  exact primeHecke_bad_square N k hN F.val F.property p.val p.property hpN

/-- Every ramified operator is genuinely semisimple on full Mcirc. At a
square divisor it is zero; at a simple divisor it satisfies a separable
quadratic polynomial with nonzero constant coefficient. -/
theorem allHecke_bad_isSemisimple (N k : ℕ) [NeZero N] (hN : 0 < N) (hk : Even k)
    (p : Nat.Primes) (hpN : p.val ∣ N) : Module.End.IsSemisimple (allHecke N k hN hk p) := by
  by_cases hp2 : p.val^2 ∣ N
  · rw [allHecke_repeated_zero N k hN hk p hp2]
    exact Module.End.isSemisimple_zero
  · let c : ℂ := (p.val : ℂ)^((k : ℤ)-2)
    have hc : c ≠ 0 := zpow_ne_zero _ (by exact_mod_cast p.property.ne_zero)
    have hs := (Polynomial.separable_X_pow_sub_C (n := 2) c (by norm_num) hc).squarefree
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      allHecke_bad_square N k hN hk p hpN]
    simp only [hp2, ite_false, Algebra.algebraMap_eq_smul_one, c, sub_self]

#print axioms allHecke_repeated_zero
#print axioms allHecke_bad_square
#print axioms allHecke_bad_isSemisimple
end QuantitativeArithmeticSmallLevelCirc
