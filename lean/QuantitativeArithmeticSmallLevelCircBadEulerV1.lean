module

public import QuantitativeArithmeticSmallLevelCircModularHeckeTheoryV4
public import QuantitativeArithmeticSmallLevelCircFactorTracesV1
public import QuantitativeArithmeticSmallLevelCircEigenPrimeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane AsymptoticClassicalCusp
open scoped ModularForm

/-- The exact ramified quadratic relation on full Mcirc, including its
noncuspidal part. -/
theorem primeHecke_bad_square (N k : ℕ) [NeZero N] (hN : 0 < N)
    (F : ModularForm (level N) (k : ℤ)) (hF : F ∈ space N hN k)
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) :
    ModularHecke.primeHecke N p hp (k : ℤ)
      (ModularHecke.primeHecke N p hp (k : ℤ) F) =
      (if p^2 ∣ N then (0 : ℂ) else (p : ℂ)^((k : ℤ)-2)) • F := by
  obtain ⟨M, rfl⟩ := hpN
  have hM : 0 < M := Nat.pos_of_mul_pos_left hN
  let : NeZero M := ⟨hM.ne'⟩
  let : Fact p.Prime := ⟨hp⟩
  have ht := factor_traces M p k hp hM F hF
  dsimp only at ht
  simp only [ModularHecke.primeHecke, Nat.dvd_mul_right p M, ite_true]
  by_cases hpM : p ∣ M
  · have hsq : p^2 ∣ p * M := by
      rw [pow_two]
      exact mul_dvd_mul_left p hpM
    simp only [hsq, ite_true, zero_smul]
    rw [ModularHecke.upperTrace_repeated_zero_of_trace M p hp hpM (k : ℤ) F ht.2, map_zero]
  · have hsq : ¬ p^2 ∣ p * M := by
      rw [pow_two, mul_dvd_mul_iff_left hp.ne_zero]
      exact hpM
    simp only [hsq, ite_false]
    have hc : p.Coprime M := hp.coprime_iff_not_dvd.mpr hpM
    have hAB : (p : ℤ) * Nat.gcdA p M + (M : ℤ) * Nat.gcdB p M = 1 := by
      have hh := Nat.gcd_eq_gcd_ab p M
      rw [hc.gcd_eq_one, Nat.cast_one] at hh
      exact hh.symm
    exact ModularHecke.upperTrace_simple_square_of_traces M p hM hpM
      (Nat.gcdA p M) (Nat.gcdB p M) hAB (k : ℤ) F ht.1 ht.2

theorem prime_eigen_bad_coefficient_square {N k : ℕ} [NeZero N] {hN : 0 < N}
    (F : space N hN k) (hone : coefficient N hN k 1 F = 1) (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes,
      ModularHecke.primeHecke N p.val p.property (k : ℤ) F.val = e p • F.val)
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) :
    (qExpansion 1 F.val).coeff p ^ 2 =
      if p^2 ∣ N then 0 else (p : ℂ)^((k : ℤ)-2) := by
  have he := heigen (⟨p, hp⟩ : Nat.Primes)
  have hs := primeHecke_bad_square N k hN F.val F.property p hp hpN
  rw [he, map_smul, he, smul_smul] at hs
  have hc := congrArg (modularCoefficient N (k : ℤ) 1) hs
  have hfirst : modularCoefficient N (k : ℤ) 1 F.val = 1 := hone
  simp only [map_smul, smul_eq_mul, hfirst, mul_one] at hc
  have hpe := (recurrence_of_prime_eigen F e heigen).prime_eigenvalue hone ⟨p, hp⟩
  rw [hpe] at hc
  exact (pow_two _).trans hc

/-- No ramified Euler assumption is needed for an actual normalized
simultaneous eigenform in full Mcirc: the two defining traces force it. -/
theorem prime_eigen_original_of_fricke {N k : ℕ} [NeZero N] {hN : 0 < N}
    (hk : 0 < k) (heven : Even k) (F : space N hN k)
    (hone : coefficient N hN k 1 F = 1) (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes,
      ModularHecke.primeHecke N p.val p.property (k : ℤ) F.val = e p • F.val)
    (eta : ℂ) (heta : eta = 1 ∨ eta = -1)
    (hfr : (F.val : ℍ → ℂ) ∣[(k : ℤ)] SmallLevelNormalized.fricke N hN =
      eta • (F.val : ℍ → ℂ)) :
    FinitenessOriginalInput.IsSolution N k (ModularLSeries.coefficients F.val) :=
  prime_eigen_isSolution hk heven F hone e heigen
    (prime_eigen_bad_coefficient_square F hone e heigen) eta heta hfr

#print axioms primeHecke_bad_square
#print axioms prime_eigen_bad_coefficient_square
#print axioms prime_eigen_original_of_fricke
end QuantitativeArithmeticSmallLevelCirc
