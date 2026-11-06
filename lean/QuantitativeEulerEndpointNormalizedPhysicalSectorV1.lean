module

public import QuantitativeEulerEndpointActualPhysicalPreservationV1
public import QuantitativeHolomorphicNormalizedSectorV1
public import QuantitativeEulerEndpointSectorProjectionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSector
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticFiniteBranch ContinuousLinearMap
open QuantitativeEulerEndpointCommonReconstruction
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (hN : 0<N) (h : ℕ) (e : Sector N)

/-- The entire actual coefficient sector in normalized terminal coordinates. -/
def normalizedPhysicalSectorMap :
    AsymptoticRamifiedSectors.sector N h
      (h+1+(AsymptoticReconstructedCount.parameters A P).s) e →ₗ[ℂ]
        AsymptoticHyperbolicSlash.Space :=
  (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε).toLinearMap.comp
    (normalizedSectorCoordinates A hN P h e)

theorem normalizedPhysicalSectorMap_reconstruct
    (a : AsymptoticRamifiedSectors.sector N h
      (h+1+(AsymptoticReconstructedCount.parameters A P).s) e) :
    physicalExact A P hN h e (normalizedPhysicalSectorMap A P hN h e a)=
      physicalSectorMap (AsymptoticReconstructedCount.parameters A P) h e a := by
  have hs := congrArg (fun T => T (normalizedSectorCoordinates A hN P h e a))
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self (AsymptoticReconstructedCount.parameters A P).ε)
  change (AsymptoticCylinderTerminal.ambientLift _).adjoint
    (AsymptoticCylinderTerminal.ambientLift _ (normalizedSectorCoordinates A hN P h e a))=
      normalizedSectorCoordinates A hN P h e a at hs
  change AsymptoticCylinderLift.lift (normalizedCountReconstruction A hN P h e
    ((AsymptoticCylinderTerminal.ambientLift _).adjoint
      (AsymptoticCylinderTerminal.ambientLift _ (normalizedSectorCoordinates A hN P h e a))))=_
  rw [hs,normalizedSectorCoordinates_reconstruct]
  rfl

theorem normalizedPhysicalSectorMap_injective :
    Function.Injective (normalizedPhysicalSectorMap A P hN h e) := by
  intro a b hab
  apply physicalSectorMap_injective (AsymptoticReconstructedCount.parameters A P) h e
  simpa only [normalizedPhysicalSectorMap_reconstruct] using congrArg (physicalExact A P hN h e) hab

theorem normalizedPhysicalSectorMap_finrank :
    Module.finrank ℂ (LinearMap.range (normalizedPhysicalSectorMap A P hN h e))=
      Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h
        (h+1+(AsymptoticReconstructedCount.parameters A P).s) e) :=
  LinearMap.finrank_range_of_inj (normalizedPhysicalSectorMap_injective A P hN h e)

theorem normalizedPhysicalSector_finiteDimensional :
    FiniteDimensional ℂ (LinearMap.range (normalizedPhysicalSectorMap A P hN h e)) := by
  let _ := AsymptoticRamifiedSectors.sector_finiteDimensional hN A
    (AsymptoticReconstructedCount.parameters A P) h
    (h+1+(AsymptoticReconstructedCount.parameters A P).s) e
  exact Module.Finite.range _

def normalizedPhysicalSectorProjection :
    AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space := by
  let _ := normalizedPhysicalSector_finiteDimensional A P hN h e
  exact (LinearMap.range (normalizedPhysicalSectorMap A P hN h e)).starProjection

theorem normalizedPhysicalSectorProjection_mem (v : AsymptoticHyperbolicSlash.Space) :
    normalizedPhysicalSectorProjection A P hN h e v∈LinearMap.range (normalizedPhysicalSectorMap A P hN h e) := by
  let _ := normalizedPhysicalSector_finiteDimensional A P hN h e
  exact (LinearMap.range (normalizedPhysicalSectorMap A P hN h e)).starProjection_apply_mem v

theorem normalizedPhysicalSectorProjection_norm : ‖normalizedPhysicalSectorProjection A P hN h e‖≤1 := by
  let _ := normalizedPhysicalSector_finiteDimensional A P hN h e
  exact (LinearMap.range (normalizedPhysicalSectorMap A P hN h e)).starProjection_norm_le

theorem normalizedPhysicalSectorProjection_terminal :
    holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) (h+1)*
      normalizedPhysicalSectorProjection A P hN h e=normalizedPhysicalSectorProjection A P hN h e := by
  rw [QuantitativeEulerEndpointTerminalExpression.unit_physical]
  change AsymptoticCylinderTerminal.hyperProjection (AsymptoticReconstructedCount.parameters A P).ε*_= _
  rw [←AsymptoticCylinderTerminal.ambientLift_self_adjoint]
  ext1 v
  obtain ⟨a,ha⟩ := normalizedPhysicalSectorProjection_mem A P hN h e v
  change AsymptoticCylinderTerminal.ambientLift _ ((AsymptoticCylinderTerminal.ambientLift _).adjoint
    (normalizedPhysicalSectorProjection A P hN h e v))=normalizedPhysicalSectorProjection A P hN h e v
  rw [←ha]
  have hs := congrArg (fun T => T (normalizedSectorCoordinates A hN P h e a))
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self (AsymptoticReconstructedCount.parameters A P).ε)
  exact congrArg (AsymptoticCylinderTerminal.ambientLift _) hs

#print axioms normalizedPhysicalSectorMap_reconstruct
#print axioms normalizedPhysicalSectorMap_finrank
#print axioms normalizedPhysicalSectorProjection_norm
#print axioms normalizedPhysicalSectorProjection_terminal
end QuantitativeEulerEndpointSector
