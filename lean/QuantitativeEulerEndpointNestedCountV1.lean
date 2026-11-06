module

public import QuantitativeEulerEndpointNestedPhysicalV1
public import QuantitativeHolomorphicSectorFilterTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointNestedPhysical
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation AsymptoticCompactObservationCount
open AsymptoticDiagonalTrace InnerProductSpace QuantitativeHolomorphic
open Polynomial QuantitativeEulerEndpointBernstein
open scoped InnerProduct

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- A positive bounded operator fixing the normalized full sector controls its dimension.
No restriction to a finite vertical band occurs in this statement. -/
theorem sector_finrank_le_positive_trace (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (F : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε →L[ℂ]
      AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (hF : 0≤F)
    (hfixF : ∀ a, F (normalizedSectorCoordinates A hN P h e a)=normalizedSectorCoordinates A hN P h e a) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let W := holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e) : ℝ) ≤
      trace fb (compressedSandwich (normalizedCountReconstruction A hN P h e) F W) := by
  intro P' W fb
  let U := normalizedCountReconstruction A hN P h e
  let C := AsymptoticRamifiedSectors.cylinderMap N h (h+1+P'.s) (P'.s+4) e P'.epsilon_pos (by omega)
  let T := compressedSandwich U F W
  have hpositive : T.IsPositive := by
    have hh := (nonneg_iff_isPositive.mp hF).adjoint_conj (U.adjoint.comp W.subtypeL)
    simpa only [T,compressedSandwich,adjoint_comp,adjoint_adjoint,ContinuousLinearMap.comp_assoc] using hh
  have hsum : Summable (fun l => (⟪T (fb l),fb l⟫_ℂ).re) :=
    compressedSandwich_summable U F W fb (2*h) (P'.s+4)
      (by positivity : 0<4*Real.pi) P'.epsilon_pos
      (normalizedCountReconstruction_fourier_gram A hN P h e)
  have hfix : ∀ w ∈ LinearMap.range C,T w=w := by
    rintro w ⟨a,rfl⟩
    change W.subtypeL.adjoint (U (F (normalizedSectorCoordinates A hN P h e a)))=C a
    rw [hfixF,normalizedSectorCoordinates_reconstruct,W.adjoint_subtypeL]
    exact W.orthogonalProjectionOnto_mem_subspace_eq_self (C a)
  let := AsymptoticRamifiedSectors.sector_finiteDimensional hN A P h (h+1+P'.s) e
  have hfin := finrank_le_trace fb T hpositive (LinearMap.range C) hfix hsum
  rw [AsymptoticRamifiedSectors.cylinderMap_finrank] at hfin
  exact hfin

/-- The actual nested positive polynomial filter bounds the literal physical sector.
All positivity, Fourier summability and exact sector invariance premises are discharged. -/
theorem sector_finrank_le_nested_trace {ι : Type*} (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : ℕ → Finset ι) (r : ℕ → ι → Row N) (s : ℕ → ι → Set UpperHalfPlane)
    (hs : ∀ j i,IsCompact (s j i)) (q₀ : ℝ[X]) (d : ℕ → ℕ) (q : ℕ → ℝ[X])
    (hq₀ : ScalarInitializer q₀) (hq : ∀ j,ScalarSharpening (q j)) (n : ℕ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let W := holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e) : ℝ) ≤
      trace fb (compressedSandwich (normalizedCountReconstruction A hN P h e)
        (filter A hN P h e qs r s hs q₀ d q n) W) :=
  sector_finrank_le_positive_trace A hN P h e _
    (filter_order A hN P h e qs r s hs q₀ d q hq₀ hq n).1
    (filter_sector_fixes A hN P h e qs r s hs q₀ d q hq₀ hq n)

#print axioms sector_finrank_le_positive_trace
#print axioms sector_finrank_le_nested_trace
end QuantitativeEulerEndpointNestedPhysical
