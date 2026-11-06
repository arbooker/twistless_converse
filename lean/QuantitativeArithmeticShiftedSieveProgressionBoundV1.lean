module

public import QuantitativeArithmeticShiftedSieveProgressionV1
public import QuantitativeArithmeticShiftedSieveDenominatorProductV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticShiftedSieveProgression
open QuantitativeArithmetic

/-- The actual number of primes in one residue class up to a natural cutoff. -/
def progressionPrimeCount (R b x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => Nat.ModEq R n b ∧ n.Prime)).card

/-- Selberg's bound applied to the literal arithmetic progression, with
all sieve data and remainder estimates discharged. -/
theorem progressionPrimeCount_sieve_bound (R b x z : ℕ) (hR : 0 < R) (hz : 1 ≤ z) :
    (progressionPrimeCount R b x : ℝ) ≤
      ((x : ℝ)/(R : ℝ))/shiftedSieveDenominator R z+(z : ℝ)^4+(z : ℝ) := by
  let P := shiftedSievePrimeProduct R z
  have hP : Squarefree P := shiftedSievePrimeProduct_squarefree R z
  let s := progressionSieve R b x P hP
  have hrem : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ 1 := by
    intro d hd
    apply progressionSieve_rem_bound R b x P hR hP (shiftedSievePrimeProduct_coprime R z).symm
    exact (Nat.mem_divisors.mp hd).1
  have hs := shiftedSieveWeights_sifted_bound s (progressionSieve_nu R b x P hP) z hz hrem
  have hsmall : ∀ p : ℕ, p.Prime → p ∣ P → p ≤ z := by
    intro p hp hd
    exact ((prime_dvd_shiftedSievePrimeProduct hp).mp hd).1
  have hc := progression_prime_count_le_sifted R b x P z hP hsmall
  have hh : (progressionPrimeCount R b x : ℝ) ≤
      s.totalMass/divisorSieveDenominator s.prodPrimes z+(z : ℝ)^4+(z : ℝ) := by
    change (progressionPrimeCount R b x : ℝ) ≤ s.siftedSum+(z : ℝ) at hc
    linarith
  simpa only [progressionPrimeCount, s, progressionSieve, P,
    divisorSieveDenominator_shiftedSievePrimeProduct] using hh

/-- An explicit uniform progression bound with the totient and logarithm.
No prime-number theorem or prime-density hypothesis occurs. -/
theorem progressionPrimeCount_log_bound (R b x z : ℕ) (hR : 0 < R)
    (hz : 1 < z) (hRz : R^2 ≤ z) :
    (progressionPrimeCount R b x : ℝ) ≤
      4*(x : ℝ)/((Nat.totient R : ℝ)*Real.log (z : ℝ))+(z : ℝ)^4+(z : ℝ) := by
  have hlog : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
  have hphi : (0 : ℝ) < Nat.totient R := by exact_mod_cast Nat.totient_pos.mpr hR
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hd : 0 < (Nat.totient R : ℝ)/(4*(R : ℝ))*Real.log (z : ℝ) := by positivity
  have hlow := shiftedSieveDenominator_log_lower R z hR hRz
  have hdiv := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ (x : ℝ)/(R : ℝ) by positivity) hd hlow
  have he : ((x : ℝ)/(R : ℝ))/((Nat.totient R : ℝ)/(4*(R : ℝ))*Real.log (z : ℝ)) =
      4*(x : ℝ)/((Nat.totient R : ℝ)*Real.log (z : ℝ)) := by
    field_simp
  rw [he] at hdiv
  have hh := progressionPrimeCount_sieve_bound R b x z hR hz.le
  linarith

#print axioms progressionPrimeCount_sieve_bound
#print axioms progressionPrimeCount_log_bound
end QuantitativeArithmeticShiftedSieveProgression
