module

public import QuantitativeEulerEndpointBaselineExclusionsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open QuantitativeEulerDensityGenerators
open scoped Classical

/-- Fixed denominator exclusions for the normalized reconstruction and the
original baseline rows. This finite set is independent of weight and blocks. -/
def reconstructionExclusions (N Q : ℕ) [NeZero N] : Finset ℕ :=
  baselineDenominators N ∪ Q.primeFactors

theorem baseline_subset_reconstructionExclusions (N Q : ℕ) [NeZero N] :
    baselineDenominators N ⊆ reconstructionExclusions N Q := Finset.subset_union_left

theorem certificate_subset_reconstructionExclusions (N Q : ℕ) [NeZero N] :
    Q.primeFactors ⊆ reconstructionExclusions N Q := Finset.subset_union_right

/-- Prepared good primes avoid every denominator of the certificate. -/
theorem good_prime_avoids_certificate {N Q : ℕ} [NeZero N] (hQ : 0<Q)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hex : Q.primeFactors⊆excluded) (q : ℕ) [Fact q.Prime] (hq : D₀.Good q) : ¬q∣Q := by
  intro hd
  exact (D₀.prime_data q (Fact.out : q.Prime) hq).1
    (hex (Nat.mem_primeFactors.mpr ⟨Fact.out,hd,hQ.ne'⟩))

#print axioms good_prime_avoids_certificate
end QuantitativeEulerEndpointPrepared
