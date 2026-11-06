module

public import AsymptoticClassicalNewDimensionDifferenceProductV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace AsymptoticClassicalDimension
open AsymptoticTotalNewCorner

/-- At a simple prime the arithmetic local factor is the elementary ratio. -/
theorem localFactor_of_simple (N p : ℕ) (hp : p.Prime) (hpN : p ∣ N)
    (hc : p.Coprime (N / p)) : localFactor N p = ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
  have hh := localFactor_mul_self (N / p) p hp (hp.coprime_iff_not_dvd.mp hc)
  rwa [Nat.mul_div_cancel' hpN] at hh

/-- Removing all simple prime old directions produces exactly the coefficient
already proved in the summed-sector analytic upper bound. -/
theorem fullDifference_arithmetic (N : ℕ) (hN : 0 < N)
    (hps : SimplePrimesAt N.primeFactors.toList N) :
    simpleDifference N.primeFactors.toList fullLeading N = arithmeticCoefficient N := by
  rw [fullDifference_product _ N hN hps, Finset.prod_map_toList]
  unfold arithmeticCoefficient fullLeading
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hh := hps.2 p (Finset.mem_toList.mpr hp)
  exact (localFactor_of_simple N p hh.1 hh.2.1 hh.2.2).symm

/-- Imposing the repeated-2 kernel first and then all odd simple primes gives
the same arithmetic coefficient, without any sector dimension formula. -/
theorem twoDifference_arithmetic (N : ℕ) (hN : 0 < N) (h4 : 4 ∣ N)
    (hps : SimplePrimesAt (N.primeFactors.erase 2).toList N) :
    simpleDifference (N.primeFactors.erase 2).toList twoLeading N = arithmeticCoefficient N := by
  have hp4 : ∀ p ∈ (N.primeFactors.erase 2).toList, p.Coprime 4 := by
    intro p hp
    have hh := hps.2 p hp
    have hne : p ≠ 2 := (Finset.mem_erase.mp (Finset.mem_toList.mp hp)).1
    have hc : p.Coprime 2 := hh.1.coprime_iff_not_dvd.mpr (by
      intro h
      exact hne ((Nat.prime_dvd_prime_iff_eq hh.1 Nat.prime_two).mp h))
    simpa using hc.pow_right 2
  have h2 : 2 ∈ N.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, dvd_trans (by decide : 2 ∣ 4) h4, hN.ne'⟩
  rw [twoDifference_product _ N hN h4 hps hp4, Finset.prod_map_toList,
    twoLeading_eq_localFactor N hN h4]
  have hprod : (∏ p ∈ N.primeFactors.erase 2, ((p : ℝ) - 1) / ((p : ℝ) + 1)) =
      ∏ p ∈ N.primeFactors.erase 2, localFactor N p := by
    apply Finset.prod_congr rfl
    intro p hp
    have hh := hps.2 p (Finset.mem_toList.mpr hp)
    exact (localFactor_of_simple N p hh.1 hh.2.1 hh.2.2).symm
  rw [hprod, mul_assoc, Finset.mul_prod_erase _ _ h2]
  rfl

#print axioms localFactor_of_simple
#print axioms fullDifference_arithmetic
#print axioms twoDifference_arithmetic
end AsymptoticClassicalDimension
