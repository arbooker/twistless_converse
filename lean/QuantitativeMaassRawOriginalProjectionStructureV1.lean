module

public import QuantitativeMaassRawOriginalTerminalProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns ContinuousLinearMap
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)

theorem sourceProjection_left_terminal :
    (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε).comp
      ((AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε).adjoint.comp
        (originalSourceProjection A P e))=originalSourceProjection A P e := by
  ext1 v
  have hv := ((originalSourceKernel A P e).starProjection_apply_mem v).1
  rw [QuantitativeEulerEndpointTerminalExpression.unit_physical] at hv
  change AsymptoticCylinderTerminal.hyperProjection (AsymptoticReconstructedCount.parameters A P).ε
    (originalSourceProjection A P e v)=originalSourceProjection A P e v at hv
  rw [←AsymptoticCylinderTerminal.ambientLift_self_adjoint] at hv
  exact hv

theorem terminalSourceProjection_selfAdjoint : IsSelfAdjoint (terminalSourceProjection A P e) := by
  have he := isSelfAdjoint_starProjection (originalSourceKernel A P e)
  apply IsSelfAdjoint.adjoint_conj he

theorem terminalSourceProjection_idempotent :
    terminalSourceProjection A P e*terminalSourceProjection A P e=terminalSourceProjection A P e := by
  let S := AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
  let E := originalSourceProjection A P e
  have hE : E.comp E=E := (originalSourceKernel A P e).isIdempotentElem_starProjection
  have hSE : S.comp (S.adjoint.comp E)=E := sourceProjection_left_terminal A P e
  change (S.adjoint.comp (E.comp S)).comp (S.adjoint.comp (E.comp S))=S.adjoint.comp (E.comp S)
  calc
    _ = S.adjoint.comp (E.comp ((S.comp (S.adjoint.comp E)).comp S)) := by simp only [comp_assoc]
    _ = S.adjoint.comp (E.comp (E.comp S)) := by rw [hSE]
    _ = _ := by rw [←comp_assoc E E S,hE]

theorem physicalExact_terminalSource_conjugate :
    let V := (EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e).toContinuousLinearMap
    V.comp ((terminalSourceProjection A P e).comp V.adjoint)=
      (physicalExact A P (NeZero.pos N) e).comp
        ((originalSourceProjection A P e).comp (physicalExact A P (NeZero.pos N) e).adjoint) := by
  intro V
  let S := AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
  have hR : physicalExact A P (NeZero.pos N) e=V.comp S.adjoint := rfl
  rw [hR,adjoint_comp,adjoint_adjoint]
  change V.comp ((S.adjoint.comp ((originalSourceProjection A P e).comp S)).comp V.adjoint)=_
  simp only [comp_assoc]

#print axioms sourceProjection_left_terminal
#print axioms terminalSourceProjection_selfAdjoint
#print axioms terminalSourceProjection_idempotent
#print axioms physicalExact_terminalSource_conjugate
end QuantitativeMaass.RawCommonReconstruction
