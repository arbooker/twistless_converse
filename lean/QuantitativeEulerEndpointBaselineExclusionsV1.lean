module

public import QuantitativeEulerEndpointBaselineRegularV1
public import QuantitativeEulerEndpointPreparedV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open QuantitativeArithmetic QuantitativeEulerDensityGenerators
open scoped Classical

/-- The finite set of denominators of the original fixed-prime rows. -/
def baselineDenominators (N : ℕ) [NeZero N] : Finset ℕ :=
  Finset.univ.image (fun a : UnitResidue N => (primeLift N a).q)

theorem good_prime_avoids_baseline {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (he : baselineDenominators N⊆excluded) (q : ℕ) [Fact q.Prime] (hq : P.Good q)
    (a : UnitResidue N) : ¬q∣(primeLift N a).q := by
  intro hd
  rcases (Nat.dvd_prime (primeLift N a).prime).mp hd with h | h
  · exact (Fact.out : q.Prime).ne_one h
  · apply (P.prime_data q (Fact.out : q.Prime) hq).1
    apply he
    rw [h]
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩

#print axioms good_prime_avoids_baseline
end QuantitativeEulerEndpointPrepared
