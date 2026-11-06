module

public import QuantitativeArithmeticShiftedSieveDenominatorV1
public import QuantitativeArithmeticShiftedSieveWeightsV1

set_option autoImplicit false
set_option maxHeartbeats 600000

@[expose] public noncomputable section
namespace QuantitativeArithmetic

open Finset

/-- Auxiliary sieve primes up to the natural cutoff, excluding modulus factors. -/
def shiftedSievePrimes (R z : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 z).filter (fun p => p.Prime ∧ ¬ p ∣ R)

def shiftedSievePrimeProduct (R z : ℕ) : ℕ := ∏ p ∈ shiftedSievePrimes R z, p

theorem mem_shiftedSievePrimes {R z p : ℕ} :
    p ∈ shiftedSievePrimes R z ↔ p.Prime ∧ p ≤ z ∧ ¬ p ∣ R := by
  classical
  simp only [shiftedSievePrimes, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨_, hpz⟩, hprime, hnot⟩
    exact ⟨hprime, hpz, hnot⟩
  · rintro ⟨hprime, hpz, hnot⟩
    exact ⟨⟨hprime.one_lt.le, hpz⟩, hprime, hnot⟩

theorem shiftedSievePrimeProduct_squarefree (R z : ℕ) :
    Squarefree (shiftedSievePrimeProduct R z) := by
  unfold shiftedSievePrimeProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (mem_shiftedSievePrimes.mp hp).1.squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (mem_shiftedSievePrimes.mp hp).1
    (mem_shiftedSievePrimes.mp hq).1).mpr hpq

theorem shiftedSievePrimeProduct_coprime (R z : ℕ) :
    Nat.Coprime (shiftedSievePrimeProduct R z) R := by
  unfold shiftedSievePrimeProduct
  apply Nat.Coprime.prod_left
  intro p hp
  have hh := mem_shiftedSievePrimes.mp hp
  exact hh.1.coprime_iff_not_dvd.mpr hh.2.2

theorem prime_dvd_shiftedSievePrimeProduct {R z p : ℕ} (hp : p.Prime) :
    p ∣ shiftedSievePrimeProduct R z ↔ p ≤ z ∧ ¬ p ∣ R := by
  unfold shiftedSievePrimeProduct
  rw [hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hdvd⟩
    have hqq := mem_shiftedSievePrimes.mp hq
    have heq : p = q := (Nat.dvd_prime hqq.1).mp hdvd |>.resolve_left hp.ne_one
    simpa only [heq] using hqq.2
  · intro hh
    exact ⟨p, mem_shiftedSievePrimes.mpr ⟨hp, hh⟩, dvd_rfl⟩

/-- Precisely the squarefree coprime integers up to z divide the sieve product. -/
theorem dvd_shiftedSievePrimeProduct_iff {R z n : ℕ} (hn : 0 < n) (hnz : n ≤ z) :
    n ∣ shiftedSievePrimeProduct R z ↔ Squarefree n ∧ Nat.Coprime n R := by
  constructor
  · intro hd
    exact ⟨(shiftedSievePrimeProduct_squarefree R z).squarefree_of_dvd hd,
      (shiftedSievePrimeProduct_coprime R z).of_dvd_left hd⟩
  · rintro ⟨hsq, hcop⟩
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    unfold shiftedSievePrimeProduct
    apply prod_dvd_prod_of_subset
    intro p hp
    have hh := Nat.mem_primeFactors.mp hp
    apply mem_shiftedSievePrimes.mpr
    exact ⟨hh.1, (Nat.le_of_dvd hn hh.2.1).trans hnz,
      hh.1.coprime_iff_not_dvd.mp (hcop.of_dvd_left hh.2.1)⟩

theorem shiftedSievePrimeProduct_filtered_divisors (R z : ℕ) :
    ((shiftedSievePrimeProduct R z).divisors.filter (fun n => n ≤ z)) =
      (Icc 1 z).filter (fun n => Squarefree n ∧ Nat.Coprime n R) := by
  classical
  have hP := (shiftedSievePrimeProduct_squarefree R z).ne_zero
  ext n
  simp only [mem_filter, Nat.mem_divisors, mem_Icc]
  constructor
  · rintro ⟨⟨hd, _⟩, hnz⟩
    have hn : 0 < n := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hd)
    exact ⟨⟨hn, hnz⟩, (dvd_shiftedSievePrimeProduct_iff hn hnz).mp hd⟩
  · rintro ⟨⟨hn, hnz⟩, hh⟩
    exact ⟨⟨(dvd_shiftedSievePrimeProduct_iff hn hnz).mpr hh, hP⟩, hnz⟩

/-- Identifies the optimal-weight denominator with the literal coprime
squarefree sum whose lower bound has already been proved. -/
theorem divisorSieveDenominator_shiftedSievePrimeProduct (R z : ℕ) :
    divisorSieveDenominator (shiftedSievePrimeProduct R z) z =
      shiftedSieveDenominator R z := by
  classical
  unfold divisorSieveDenominator shiftedSieveDenominator
  rw [← sum_filter, shiftedSievePrimeProduct_filtered_divisors, sum_filter]

#print axioms shiftedSievePrimeProduct_squarefree
#print axioms shiftedSievePrimeProduct_coprime
#print axioms prime_dvd_shiftedSievePrimeProduct
#print axioms divisorSieveDenominator_shiftedSievePrimeProduct

end QuantitativeArithmetic
