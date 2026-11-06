module

public import QuantitativeEulerEndpointCommonReconstructionV1
public import QuantitativeEulerEndpointTerminalUnitExpressionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticFiniteBranch ContinuousLinearMap

theorem transport_right_projection {J K H : Type*}
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : K →L[ℂ] H) (V : J →L[ℂ] K) (S : J →L[ℂ] H)
    (hS : S.adjoint.comp S=1) :
    (L.comp (V.comp S.adjoint)).comp (S.comp S.adjoint)=L.comp (V.comp S.adjoint) := by
  ext1 v
  have hv := congrArg (fun W : J →L[ℂ] J => W (S.adjoint v)) hS
  change S.adjoint (S (S.adjoint v))=S.adjoint v at hv
  change L (V (S.adjoint (S (S.adjoint v))))=L (V (S.adjoint v))
  exact congrArg (fun w => L (V w)) hv

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- The physical common reconstruction has exactly the entire terminal
source, before any upper truncation for a trace estimate. -/
theorem physical_right_terminal (hN : 0<N) (s : ℝ) (e : Sector N) (h : ℕ) :
    holomorphicSum (expression A P hN s e) (h+1)*
      holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) (h+1)=
        holomorphicSum (expression A P hN s e) (h+1) := by
  rw [QuantitativeEulerEndpointTerminalExpression.unit_physical]
  change holomorphicSum (expression A P hN s e) (h+1)*
      AsymptoticCylinderTerminal.hyperProjection (AsymptoticReconstructedCount.parameters A P).ε=_
  rw [←AsymptoticCylinderTerminal.ambientLift_self_adjoint]
  dsimp only [expression]
  rw [holomorphicSum_normalizedCutCountExpression]
  exact transport_right_projection _ _ _ (AsymptoticCylinderTerminal.ambientLift_adjoint_self _)

#print axioms transport_right_projection
#print axioms physical_right_terminal
end QuantitativeEulerEndpointCommonReconstruction
