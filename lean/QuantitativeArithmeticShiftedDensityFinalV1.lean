module

public import QuantitativeArithmeticShiftedDensityFinalCoreV1
public import QuantitativeArithmeticShiftedDensityPacketV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic

/-- Almost every prime has a prime divisor of its nonzero fixed shift in
any prescribed unit residue class. All distribution inputs are proved:
Dirichlet reciprocal divergence, finite CRT, a fixed-modulus Selberg upper
bound, and an absolute Chebyshev lower bound for the primes. -/
theorem relativePrimeDensityOne_prime_shifted_class
    (Q M : ℕ) (hQ : 0 < Q) (hM : 0 < M) (a : ZMod M) (ha : IsUnit a) :
    RelativePrimeDensityOne (fun p => ∃ l : ℕ,
      l.Prime ∧ (l : ZMod M) = a ∧ (l : ℤ) ∣ ((p : ℤ) - (Q : ℤ))) := by
  apply relativePrimeDensityOne_prime_shifted_class_of_packet_bound Q M hQ hM a ha
  intro S hp hSQ
  simpa only [packetAvoidanceCount] using
    eventually_packetAvoidanceCount_upper S Q hp hSQ

#print axioms relativePrimeDensityOne_prime_shifted_class

end QuantitativeArithmetic
