module

public import QuantitativeConcreteGoalsV1
public import QuantitativeEulerEndpointProductV1
public import QuantitativeEulerEndpointBarrierV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointGoals

/-- The current user goal, with exponent ONE. This is only a proposition;
the earlier requested range delta<1/2 does not imply it. The error is the
literal Euler count minus the actual classical newspace dimension. -/
def RequestedHolomorphicEndpointTheorem : Prop :=
  ∀ (N : ℕ) (hN : GridAdmissibleGap.Admissible N),
    QuantitativeConcreteGoals.HolomorphicCountClaim N hN.1 1

/-- Verify that exponent one is precisely the user's quotient, with the
same shifted double logarithm, rather than a renamed weaker scale. -/
theorem endpoint_scale (k : ℝ) :
    QuantitativeHolomorphic.shiftedRemainderScale 1 k =
      k / Real.log (Real.log (2*k)) := by
  simp [QuantitativeHolomorphic.shiftedRemainderScale, Real.rpow_neg_one,
    div_eq_mul_inv]

#print axioms endpoint_scale

end QuantitativeEulerEndpointGoals
