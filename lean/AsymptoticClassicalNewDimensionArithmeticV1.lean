module

public import AsymptoticClassicalNewDimensionDifferenceV1
public import AsymptoticArithmeticNewCoefficientV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace AsymptoticClassicalDimension

open AsymptoticCongruenceStrip AsymptoticTotalNewCorner

/-- The congruence index multiplies by p+1 at a new prime. -/
theorem full_index_mul_prime (M p : ℕ) (hM : 0 < M) (hp : p.Prime) (hpM : ¬ p ∣ M) :
    (gamma (p * M)).relIndex (gamma 1) = (p + 1) * (gamma M).relIndex (gamma 1) := by
  have hh := Subgroup.relIndex_mul_relIndex (gamma (p * M)) (gamma M) (gamma 1)
    (gamma_le_of_dvd (Nat.dvd_mul_left M p)) (gamma_le_of_dvd (one_dvd M))
  rw [AsymptoticRamifiedCosets.projective_index_coprime M p hM hp
    (hp.coprime_iff_not_dvd.mpr hpM)] at hh
  exact hh.symm

theorem fullLeading_mul_prime (M p : ℕ) (hM : 0 < M) (hp : p.Prime) (hpM : ¬ p ∣ M) :
    fullLeading (p * M) = ((p : ℝ) + 1) * fullLeading M := by
  rw [fullLeading, full_index_mul_prime M p hM hp hpM, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  unfold fullLeading
  ring

/-- Factors belonging to other primes are unchanged by inserting a coprime prime. -/
theorem localFactor_mul_other (M p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) :
    localFactor (p * M) q = localFactor M q := by
  have hc : q.Coprime p := hq.coprime_iff_not_dvd.mpr (by
    intro h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h))
  simp only [localFactor, (hc.pow_left 2).dvd_mul_left, (hc.pow_left 3).dvd_mul_left]

theorem localFactor_mul_self (M p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M) :
    localFactor (p * M) p = ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
  have hsq : ¬ p^2 ∣ p * M := by
    rw [pow_two, Nat.mul_dvd_mul_iff_left hp.pos]
    exact hpM
  simp only [localFactor, hsq, ite_false]

/-- The arithmetic new coefficient multiplies by p-1 at a simple new prime. -/
theorem arithmeticCoefficient_mul_prime (M p : ℕ) (hM : 0 < M) (hp : p.Prime)
    (hpM : ¬ p ∣ M) : arithmeticCoefficient (p * M) = ((p : ℝ) - 1) * arithmeticCoefficient M := by
  classical
  have hnot : p ∉ M.primeFactors := fun h => hpM (Nat.mem_primeFactors.mp h).2.1
  have hprod : (∏ q ∈ M.primeFactors, localFactor (p * M) q) =
      ∏ q ∈ M.primeFactors, localFactor M q := by
    apply Finset.prod_congr rfl
    intro q hq
    have hqp : q ≠ p := by intro h; subst q; exact hnot hq
    exact localFactor_mul_other M p q hp (Nat.mem_primeFactors.mp hq).1 hqp
  unfold arithmeticCoefficient
  rw [Nat.primeFactors_mul hp.ne_zero hM.ne', hp.primeFactors, Finset.singleton_union,
    Finset.prod_insert hnot, localFactor_mul_self M p hp hpM, hprod,
    full_index_mul_prime M p hM hp hpM, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hd : (p : ℝ) + 1 ≠ 0 := by positivity
  field_simp

#print axioms full_index_mul_prime
#print axioms fullLeading_mul_prime
#print axioms localFactor_mul_other
#print axioms localFactor_mul_self
#print axioms arithmeticCoefficient_mul_prime
end AsymptoticClassicalDimension
