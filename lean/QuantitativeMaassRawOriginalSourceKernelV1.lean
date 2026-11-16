module

public import QuantitativeMaassRawActualPhysicalResidualV1
public import QuantitativeMaassRawOriginalRowFamilyV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open ContinuousLinearMap AsymptoticFiniteBranch AsymptoticCompactObservationCount
open MeasureTheory
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)

/-- The closed full-terminal kernel of all actual original observation rows. -/
def originalSourceKernel : Submodule ℂ AsymptoticHyperbolicSlash.Space where
  carrier := {v | holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) 0 v=v ∧
    ∀ (row : Row N) (s : Set UpperHalfPlane) (hs : IsCompact s),
      holomorphicSum (rowExpression (NeZero.pos N) row e hs
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+3)) 0
          (physicalExact A P (NeZero.pos N) e v)=0}
  zero_mem' := by
    constructor
    · exact map_zero _
    · intro row s hs
      rw [map_zero,map_zero]
  add_mem' := by
    intro v w hv hw
    refine ⟨by rw [map_add,hv.1,hw.1],?_⟩
    intro row s hs
    rw [map_add,map_add,hv.2 row s hs,hw.2 row s hs,add_zero]
  smul_mem' := by
    intro c v hv
    refine ⟨by rw [map_smul,hv.1],?_⟩
    intro row s hs
    rw [map_smul,map_smul,hv.2 row s hs,smul_zero]

theorem originalSourceKernel_closed : IsClosed (originalSourceKernel A P e : Set AsymptoticHyperbolicSlash.Space) := by
  change IsClosed {v | holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) 0 v=v ∧
    ∀ (row : Row N) (s : Set UpperHalfPlane) (hs : IsCompact s),
      holomorphicSum (rowExpression (NeZero.pos N) row e hs
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+3)) 0
          (physicalExact A P (NeZero.pos N) e v)=0}
  simp only [Set.ofPred_and,Set.ofPred_forall]
  exact (isClosed_eq (holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) 0).continuous
    continuous_id).inter (isClosed_iInter (fun row => isClosed_iInter (fun s => isClosed_iInter (fun hs =>
      ((holomorphicSum (rowExpression (NeZero.pos N) row e hs
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+3)) 0).comp
          (physicalExact A P (NeZero.pos N) e)).isClosed_ker))))

instance originalSourceKernel_complete : CompleteSpace (originalSourceKernel A P e) :=
  (originalSourceKernel_closed A P e).completeSpace_coe

def originalSourceProjection := (originalSourceKernel A P e).starProjection

theorem originalSourceProjection_norm : ‖originalSourceProjection A P e‖≤1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  simpa only [originalSourceProjection,one_mul] using (originalSourceKernel A P e).norm_starProjection_apply_le v

theorem physicalExact_ambient_terminal
    (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) :
    physicalExact A P (NeZero.pos N) e
      (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε g)=
      EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e g := by
  let S := AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
  have hv := congrArg (fun T => T g) (AsymptoticCylinderTerminal.ambientLift_adjoint_self
    (AsymptoticReconstructedCount.parameters A P).ε)
  change S.adjoint (S g)=g at hv
  change AsymptoticCylinderLift.lift (EulerHilbert.normalized A (NeZero.pos N) P e (S.adjoint (S g)))=_
  rw [hv]
  rfl

omit [NeZero N] in
theorem terminal_unit_ambient
    (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) :
    holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) 0
      (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε g)=
      AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε g := by
  rw [QuantitativeEulerEndpointTerminalExpression.unit_physical]
  change AsymptoticCylinderTerminal.hyperProjection (AsymptoticReconstructedCount.parameters A P).ε _=_
  rw [←AsymptoticCylinderTerminal.ambientLift_self_adjoint]
  have hv := congrArg (fun T => T g) (AsymptoticCylinderTerminal.ambientLift_adjoint_self
    (AsymptoticReconstructedCount.parameters A P).ε)
  exact congrArg (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε) hv

#print axioms originalSourceKernel_closed
#print axioms originalSourceProjection_norm
#print axioms physicalExact_ambient_terminal
#print axioms terminal_unit_ambient
end QuantitativeMaass.RawCommonReconstruction
