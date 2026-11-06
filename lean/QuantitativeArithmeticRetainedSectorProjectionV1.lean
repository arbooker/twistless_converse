module

public import QuantitativeArithmeticRetainedEulerCylinderV1
public import AsymptoticCylinderTerminalLiftV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedSectorProjection

open ContinuousLinearMap AsymptoticSectorSigns AsymptoticCylinder
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedSectorReconstruction
open QuantitativeArithmeticRetainedCylinderNormalization

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (hS : ∀p∈S,p.Prime) (hN : 0<N) (P : Parameters A)
    (h d t : ℕ) (ht : 2≤t) (hd : 2*d+4≤2*h+2*t+1) (e : Sector N)

def coordinates : AsymptoticRamifiedSectors.sector N h d e →ₗ[ℂ]
    AsymptoticCylinderTerminal.Space P.ε :=
  (normalized A hS hN P (multiplier e) (ramifiedParameter e) ht (h+1)).adjoint.toLinearMap.comp
    ((holomorphicSpace (2*h) (t+1) (by positivity : 0<4*Real.pi) P.epsilon_pos).subtype.comp
      (AsymptoticRamifiedSectors.cylinderMap N h d (t+1) e P.epsilon_pos (by omega)))

theorem coordinates_reconstruct (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N)
    (hK : ‖QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P
      (multiplier e) (ramifiedParameter e) t (h+1)‖<1/2)
    (a : AsymptoticRamifiedSectors.sector N h d e) :
    normalized A hS hN P (multiplier e) (ramifiedParameter e) ht (h+1)
      (coordinates A hS hN P h d t ht hd e a)=
      (AsymptoticRamifiedSectors.cylinderMap N h d (t+1) e P.epsilon_pos (by omega) a:Space) := by
  let w := AsymptoticRamifiedSectors.cylinderMap N h d (t+1) e P.epsilon_pos (by omega) a
  obtain ⟨g,hg⟩ := sector_normalized A hS hN P hdiv hbad h d t ht hd e hK w ⟨a,rfl⟩
  have hgram := QuantitativeHolomorphic.normalizedReconstruction_gram
    (scaled A hS hN P (multiplier e) (ramifiedParameter e) ht (h+1)) (gramLower_pos A P)
    (scaled_bounds A hS hN P (multiplier e) (ramifiedParameter e)
      (fun q _ => multiplier_norm e q) (fun p _ => ramifiedParameter_norm e p) ht (h+1) hK).2
  have hv := congrArg (fun T => T g) hgram
  change (normalized A hS hN P (multiplier e) (ramifiedParameter e) ht (h+1)).adjoint
    (normalized A hS hN P (multiplier e) (ramifiedParameter e) ht (h+1) g)=g at hv
  change normalized A hS hN P (multiplier e) (ramifiedParameter e) ht (h+1)
    ((normalized A hS hN P (multiplier e) (ramifiedParameter e) ht (h+1)).adjoint (w:Space))=(w:Space)
  rw [←hg,hv]

theorem coordinates_injective (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N)
    (hK : ‖QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P
      (multiplier e) (ramifiedParameter e) t (h+1)‖<1/2) :
    Function.Injective (coordinates A hS hN P h d t ht hd e) := by
  intro a b hab
  have he := congrArg (normalized A hS hN P (multiplier e) (ramifiedParameter e) ht (h+1)) hab
  rw [coordinates_reconstruct A hS hN P h d t ht hd e hdiv hbad hK,
    coordinates_reconstruct A hS hN P h d t ht hd e hdiv hbad hK] at he
  exact AsymptoticRamifiedSectors.cylinderMap_injective N h d (t+1) e P.epsilon_pos
    (by omega) (Subtype.ext he)

/-- The full original linear sector in the terminal hyperbolic-strip
realization, after the common Gram normalization. -/
def physicalMap : AsymptoticRamifiedSectors.sector N h d e →ₗ[ℂ]
    AsymptoticHyperbolicSlash.Space :=
  (AsymptoticCylinderTerminal.ambientLift P.ε).toLinearMap.comp
    (coordinates A hS hN P h d t ht hd e)

theorem physicalMap_injective (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N)
    (hK : ‖QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P
      (multiplier e) (ramifiedParameter e) t (h+1)‖<1/2) :
    Function.Injective (physicalMap A hS hN P h d t ht hd e) := by
  intro a b hab
  apply coordinates_injective A hS hN P h d t ht hd e hdiv hbad hK
  have he := congrArg (AsymptoticCylinderTerminal.ambientLift P.ε).adjoint hab
  have ha := congrArg (fun T => T (coordinates A hS hN P h d t ht hd e a))
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self P.ε)
  have hb := congrArg (fun T => T (coordinates A hS hN P h d t ht hd e b))
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self P.ε)
  exact ha.symm.trans (he.trans hb)

theorem physicalMap_finrank (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N)
    (hK : ‖QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P
      (multiplier e) (ramifiedParameter e) t (h+1)‖<1/2) :
    Module.finrank ℂ (LinearMap.range (physicalMap A hS hN P h d t ht hd e))=
      Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h d e) :=
  LinearMap.finrank_range_of_inj (physicalMap_injective A hS hN P h d t ht hd e hdiv hbad hK)

theorem physicalMap_finiteDimensional (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N) :
    FiniteDimensional ℂ (LinearMap.range (physicalMap A hS hN P h d t ht hd e)) := by
  let _ := sector_finiteDimensional A hS hN P hdiv hbad h d e
  exact Module.Finite.range _

def projection (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N) :
    AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space := by
  let _ := physicalMap_finiteDimensional A hS hN P h d t ht hd e hdiv hbad
  exact (LinearMap.range (physicalMap A hS hN P h d t ht hd e)).starProjection

theorem projection_mem (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N)
    (v : AsymptoticHyperbolicSlash.Space) :
    projection A hS hN P h d t ht hd e hdiv hbad v∈
      LinearMap.range (physicalMap A hS hN P h d t ht hd e) := by
  let _ := physicalMap_finiteDimensional A hS hN P h d t ht hd e hdiv hbad
  exact (LinearMap.range (physicalMap A hS hN P h d t ht hd e)).starProjection_apply_mem v

theorem projection_norm (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N) :
    ‖projection A hS hN P h d t ht hd e hdiv hbad‖≤1 := by
  let _ := physicalMap_finiteDimensional A hS hN P h d t ht hd e hdiv hbad
  exact (LinearMap.range (physicalMap A hS hN P h d t ht hd e)).starProjection_norm_le

theorem projection_terminal (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N) :
    AsymptoticCylinderTerminal.hyperProjection P.ε * projection A hS hN P h d t ht hd e hdiv hbad=
      projection A hS hN P h d t ht hd e hdiv hbad := by
  rw [←AsymptoticCylinderTerminal.ambientLift_self_adjoint]
  ext1 v
  obtain ⟨a,ha⟩ := projection_mem A hS hN P h d t ht hd e hdiv hbad v
  change AsymptoticCylinderTerminal.ambientLift P.ε ((AsymptoticCylinderTerminal.ambientLift P.ε).adjoint
    (projection A hS hN P h d t ht hd e hdiv hbad v))=projection A hS hN P h d t ht hd e hdiv hbad v
  rw [←ha]
  have hs := congrArg (fun T => T (coordinates A hS hN P h d t ht hd e a))
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self P.ε)
  exact congrArg (AsymptoticCylinderTerminal.ambientLift P.ε) hs

#print axioms coordinates_reconstruct
#print axioms coordinates_injective
#print axioms physicalMap_finrank
#print axioms projection_norm
#print axioms projection_terminal
end QuantitativeArithmeticRetainedSectorProjection
