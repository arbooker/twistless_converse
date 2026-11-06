module

public import QuantitativeHolomorphicFilterTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation AsymptoticCompactObservationCount
open AsymptoticDiagonalTrace InnerProductSpace
open scoped InnerProduct

private theorem compressedSandwich_positive {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : G →L[ℂ] H) (I : G →L[ℂ] G) (hI : I.IsPositive)
    (W : Submodule ℂ H) [CompleteSpace W] : (compressedSandwich R I W).IsPositive := by
  have hh := hI.adjoint_conj (R.adjoint.comp W.subtypeL)
  simpa only [compressedSandwich, adjoint_comp, adjoint_adjoint, comp_assoc] using hh

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable {ι : Type*}

/-- The single global filter bounds the finrank of the literal full
coefficient sector.  Its positivity, fixed-vector property, Fourier trace
summability and injectivity of coefficient realization are all discharged. -/
theorem sector_finrank_le_normalized_filter_trace (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (d : ℕ) :
    (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h
      (h+1+(AsymptoticReconstructedCount.parameters A P).s) e) : ℝ) ≤
      trace (fourierBasis (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4)
        (by positivity : 0 < 4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos)
        (countObservationHolomorphicFilter A hN P h e qs r s hs
          (normalizedCountReconstruction A hN P h e) d) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let W := holomorphicSpace (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos
  let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos
  let U := normalizedCountReconstruction A hN P h e
  let F := normalizedObservationFilter A hN P h e qs r s hs d
  let C := AsymptoticRamifiedSectors.cylinderMap N h (h+1+P'.s) (P'.s+4) e P'.epsilon_pos (by omega)
  let T := countObservationHolomorphicFilter A hN P h e qs r s hs U d
  have hT : T = compressedSandwich U F W := rfl
  have hpositive : T.IsPositive := hT ▸ compressedSandwich_positive U F
    (nonneg_iff_isPositive.mp (normalizedObservationFilter_order A hN P h e qs r s hs d).1) W
  have hsum : Summable (fun l => (⟪T (fb l),fb l⟫_ℂ).re) := by
    rw [hT]
    exact compressedSandwich_summable U F W fb (2*h) (P'.s+4)
      (by positivity : 0 < 4*Real.pi) P'.epsilon_pos
      (normalizedCountReconstruction_fourier_gram A hN P h e)
  have hfix : ∀ w ∈ LinearMap.range C, T w = w := by
    rintro w ⟨a, rfl⟩
    change W.subtypeL.adjoint (U (F (normalizedSectorCoordinates A hN P h e a))) = C a
    rw [normalizedObservationFilter_sector_fixes, normalizedSectorCoordinates_reconstruct]
    rw [W.adjoint_subtypeL]
    exact W.orthogonalProjectionOnto_mem_subspace_eq_self (C a)
  let := AsymptoticRamifiedSectors.sector_finiteDimensional hN A P h (h+1+P'.s) e
  have hfin := finrank_le_trace fb T hpositive (LinearMap.range C) hfix hsum
  rw [AsymptoticRamifiedSectors.cylinderMap_finrank] at hfin
  exact hfin

/-- The literal sector dimension is bounded by the actual finite Newton
filter trace with an explicit cutoff/depth error. -/
theorem sector_finrank_le_finite_filter_trace (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (Y : ℝ) (hY : 0 ≤ Y) (j J n d : ℕ) (hJ : 0 < J)
    (hD : 0 < countFilterError A P Y j J n d) (hD1 : countFilterError A P Y j J n d ≤ 1) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos
    (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e) : ℝ) ≤
      trace fb (countObservationHolomorphicFilter A hN P h e qs r s hs
        (polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n) d) +
      (4*h+2 : ℝ) * (2 + 2 * countFilterMajorant A P n *
        majorantConstant (P'.s+4) (4*Real.pi) P'.ε) * Real.sqrt (countFilterError A P Y j J n d) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos
  let u := trace fb (countObservationHolomorphicFilter A hN P h e qs r s hs
    (normalizedCountReconstruction A hN P h e) d)
  let v := trace fb (countObservationHolomorphicFilter A hN P h e qs r s hs
    (polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n) d)
  have hdim := sector_finrank_le_normalized_filter_trace A hN P h e qs r s hs d
  have herr := countObservationHolomorphicFilter_trace_error A hN P h e qs r s hs Y hY j J n d hJ hD hD1
  have hk : (0 : ℝ) < 4*h+2 := by positivity
  have he : |v-u| ≤ (2 + 2 * countFilterMajorant A P n * majorantConstant (P'.s+4) (4*Real.pi) P'.ε) *
      Real.sqrt (countFilterError A P Y j J n d) * (4*h+2 : ℝ) :=
    (div_le_iff₀ hk).1 herr
  have hx : u-v ≤ |v-u| := by rw [abs_sub_comm]; exact le_abs_self _
  change (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e) : ℝ) ≤ u at hdim
  change (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e) : ℝ) ≤ v + _
  nlinarith only [hdim, he, hx]

#print axioms sector_finrank_le_finite_filter_trace

#print axioms sector_finrank_le_normalized_filter_trace

end QuantitativeHolomorphic
