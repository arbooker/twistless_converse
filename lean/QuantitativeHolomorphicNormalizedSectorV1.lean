module

public import QuantitativeHolomorphicNormalizationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticObservation ContinuousLinearMap

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)

/-- Linear coordinates for the literal full ramified sector in the
normalized terminal Hilbert space. -/
def normalizedSectorCoordinates (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N) :
    AsymptoticRamifiedSectors.sector N h
      (h + 1 + (AsymptoticReconstructedCount.parameters A P).s) e →ₗ[ℂ]
        AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε :=
  let P' := AsymptoticReconstructedCount.parameters A P
  (normalizedCountReconstruction A hN P h e).adjoint.toLinearMap.comp
    ((holomorphicSpace (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos).subtype.comp
      (AsymptoticRamifiedSectors.cylinderMap N h (h+1+P'.s) (P'.s+4)
        e P'.epsilon_pos (by omega)))

theorem normalizedSectorCoordinates_reconstruct (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N)
    (a : AsymptoticRamifiedSectors.sector N h
      (h + 1 + (AsymptoticReconstructedCount.parameters A P).s) e) :
    normalizedCountReconstruction A hN P h e (normalizedSectorCoordinates A hN P h e a) =
      (AsymptoticRamifiedSectors.cylinderMap N h
        (h+1+(AsymptoticReconstructedCount.parameters A P).s)
        ((AsymptoticReconstructedCount.parameters A P).s+4) e
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos (by omega) a : Space) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let w := AsymptoticRamifiedSectors.cylinderMap N h (h+1+P'.s) (P'.s+4)
    e P'.epsilon_pos (by omega) a
  have hw : w ∈ eulerCylinderSector P' h e := ⟨a, rfl⟩
  obtain ⟨g, hg⟩ := normalizedCountReconstruction_sector A hN P h e w hw
  have hgram := normalizedReconstruction_gram (scaledCountReconstruction A hN P h e)
    (countGramLower_pos A P) (scaledCountReconstruction_bounds A hN P h e).2
  have hv := congrArg (fun T => T g) hgram
  change (normalizedCountReconstruction A hN P h e).adjoint
    (normalizedCountReconstruction A hN P h e g) = g at hv
  change normalizedCountReconstruction A hN P h e
    ((normalizedCountReconstruction A hN P h e).adjoint (w : Space)) = (w : Space)
  rw [← hg, hv]

theorem normalizedSectorCoordinates_injective (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) :
    Function.Injective (normalizedSectorCoordinates A hN P h e) := by
  intro a b hab
  have he := congrArg (normalizedCountReconstruction A hN P h e) hab
  rw [normalizedSectorCoordinates_reconstruct, normalizedSectorCoordinates_reconstruct] at he
  apply AsymptoticRamifiedSectors.cylinderMap_injective N h
    (h + 1 + (AsymptoticReconstructedCount.parameters A P).s)
    ((AsymptoticReconstructedCount.parameters A P).s + 4) e
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos (by omega)
  exact Subtype.ext he

/-- In particular, terminal normalization preserves the dimension of the
full coefficient sector, the linear-space target of the quantitative proof. -/
theorem normalizedSectorCoordinates_finrank (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) :
    Module.finrank ℂ (LinearMap.range (normalizedSectorCoordinates A hN P h e)) =
      Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h
        (h + 1 + (AsymptoticReconstructedCount.parameters A P).s) e) :=
  LinearMap.finrank_range_of_inj (normalizedSectorCoordinates_injective A hN P h e)

#print axioms normalizedSectorCoordinates_reconstruct
#print axioms normalizedSectorCoordinates_injective
#print axioms normalizedSectorCoordinates_finrank

end QuantitativeHolomorphic
