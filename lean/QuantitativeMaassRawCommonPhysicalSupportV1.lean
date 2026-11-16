module

public import QuantitativeMaassRawCommonReconstructionV1
public import QuantitativeEulerEndpointCommonPhysicalSupportV1
public import QuantitativeEulerEndpointTerminalUnitExpressionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open QuantitativeMaass.EulerHilbert.FullTerminal
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticFiniteBranch ContinuousLinearMap

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- The physical common reconstruction has exactly the entire terminal
source, before any upper truncation for a trace estimate. -/
theorem physical_right_terminal (hN : 0<N) (s : ℝ) (e : Sector N) :
    holomorphicSum (expression A P hN s e) 0*
      holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) 0=
        holomorphicSum (expression A P hN s e) 0 := by
  rw [QuantitativeEulerEndpointTerminalExpression.unit_physical]
  change holomorphicSum (expression A P hN s e) 0*
      AsymptoticCylinderTerminal.hyperProjection (AsymptoticReconstructedCount.parameters A P).ε=_
  rw [←AsymptoticCylinderTerminal.ambientLift_self_adjoint]
  dsimp only [expression]
  rw [normalizedFullExpression_eq_ambient]
  exact QuantitativeEulerEndpointCommonReconstruction.transport_right_projection _ _ _ (AsymptoticCylinderTerminal.ambientLift_adjoint_self _)

#print axioms physical_right_terminal
end QuantitativeMaass.RawCommonReconstruction
