module

public import QuantitativeArithmeticAugmentedSpanningV1
public import FinitenessPaper2GrowthV1

set_option autoImplicit false

public section

namespace FinitenessAllLevelAuxiliary

open QuantitativeArithmeticRetainedCertificate

/-- The augmented reconstruction certificate with exactly one retained
good prime, for every positive level. -/
theorem certificate_at_prime {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hlarge : N < p^2) :
    ∃ Q : ℕ, ∃ hQ : 0 < Q, N ∣ Q ∧ p ∣ Q ∧
      Nonempty (Certificate N {p} Q hQ) := by
  obtain ⟨Q, hQ, hNQ, hpQ, hc⟩ :=
    QuantitativeArithmeticAugmentedSpanning.exists_certificate hN {p}
      (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hp)
      (by simpa only [Finset.prod_singleton] using hlarge)
  exact ⟨Q, hQ, hNQ, hpQ p (Finset.mem_singleton_self p), hc⟩

/-- Two distinct auxiliary primes larger than sqrt(N) exist without any
admissibility or radical hypothesis. -/
theorem two_large_good_primes (N : ℕ) (hN : 0 < N) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧
      ¬ p ∣ N ∧ ¬ r ∣ N ∧ N < p^2 ∧ N < r^2 := by
  obtain ⟨p, hp, hpN, hplarge⟩ := FinitenessPaper2.exists_large_good_prime N hN
  obtain ⟨r, hrbound, hr⟩ := Nat.exists_infinite_primes (N+p+1)
  have hNr : N < r := by omega
  refine ⟨p, r, hp, hr, by omega, hpN, ?_, hplarge, ?_⟩
  · intro hd
    exact (not_le_of_gt hNr) (Nat.le_of_dvd hN hd)
  · nlinarith [hr.two_le]

/-- Both certificates needed for the two-prime argument are available
unconditionally; each is an actual finite rational certificate. -/
theorem two_prime_certificates (N : ℕ) (hN : 0 < N) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ ¬ p ∣ N ∧ ¬ r ∣ N ∧
      (∃ Q : ℕ, ∃ hQ : 0 < Q, N ∣ Q ∧ p ∣ Q ∧
        Nonempty (Certificate N {p} Q hQ)) ∧
      (∃ Q : ℕ, ∃ hQ : 0 < Q, N ∣ Q ∧ r ∣ Q ∧
        Nonempty (Certificate N {r} Q hQ)) := by
  obtain ⟨p, r, hp, hr, hne, hpN, hrN, hplarge, hrlarge⟩ := two_large_good_primes N hN
  exact ⟨p, r, hp, hr, hne, hpN, hrN,
    certificate_at_prime hN hp hplarge, certificate_at_prime hN hr hrlarge⟩

#print axioms certificate_at_prime
#print axioms two_large_good_primes
#print axioms two_prime_certificates

end FinitenessAllLevelAuxiliary
