module

public import QuantitativeHolomorphicFilterMajorantV1
public import QuantitativeHolomorphicTracePerturbationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation AsymptoticCompactObservationCount
open AsymptoticDiagonalTrace InnerProductSpace
open scoped InnerProduct

section Compression
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def orthogonalCompression (W : Submodule ℂ H) [CompleteSpace W] (T : H →L[ℂ] H) :=
  W.subtypeL.adjoint.comp (T.comp W.subtypeL)

theorem orthogonalCompression_sub_norm_le (W : Submodule ℂ H) [CompleteSpace W]
    (T S : H →L[ℂ] H) :
    ‖orthogonalCompression W T - orthogonalCompression W S‖ ≤ ‖T-S‖ := by
  have hu : ‖W.subtypeL‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro u
    simp
  have hua : ‖W.subtypeL.adjoint‖ ≤ 1 := by rwa [adjoint.norm_map]
  change ‖W.subtypeL.adjoint.comp (T.comp W.subtypeL) - W.subtypeL.adjoint.comp (S.comp W.subtypeL)‖ ≤ _
  rw [← comp_sub, ← sub_comp]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right hua (norm_nonneg _)).trans
  rw [one_mul]
  exact (opNorm_comp_le _ _).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu (norm_nonneg (T-S)))
end Compression

section Majorant
variable {G H K ι : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem finiteRowFilter_diagonal_bound (qs : Finset ι) (L : ι → H →L[ℂ] K) (b : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ b i) (V : G →L[ℂ] H) (hV : ‖V‖ ≤ 1) (d : ℕ)
    (W : Submodule ℂ H) [CompleteSpace W] (u : W) :
    ‖(⟪orthogonalCompression W (V.comp ((finiteRowFilter qs L b V d).comp V.adjoint)) u,u⟫_ℂ).re‖ ≤
      ‖V.adjoint (u : H)‖ ^ 2 := by
  exact (compressedSandwich_diagonal_bound V (finiteRowFilter qs L b V d) W u).trans
    (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (finiteRowFilter_order qs L b hL V hV d).2.2 (sq_nonneg _))
end Majorant

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable {ι : Type*}

def countObservationHolomorphicFilter (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (V : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε →L[ℂ] Space)
    (d : ℕ) :=
  orthogonalCompression (holomorphicSpace (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4)
    (by positivity : 0 < 4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos)
    (observationCylinderFilter A hN P h e qs r s hs V d)

def countFilterMajorant (P : Parameters A) (n : ℕ) : ℝ :=
  max (((Real.sqrt (countGramLower A P))⁻¹)^2) (((4 : ℝ)^(4^n))^2)

def countFilterError (P : Parameters A) (Y : ℝ) (j J n d : ℕ) : ℝ :=
  (2*d+2 : ℝ) * normalizedCutError A P Y j J n

/-- The actual holomorphic trace error has no analytic majorant hypothesis.
Only the explicit scalar choices making the error lie in (0,1] are required. -/
theorem countObservationHolomorphicFilter_trace_error (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (Y : ℝ) (hY : 0 ≤ Y) (j J n d : ℕ) (hJ : 0 < J)
    (hD : 0 < countFilterError A P Y j J n d) (hD1 : countFilterError A P Y j J n d ≤ 1) :
    let fb := fourierBasis (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4)
      (by positivity : 0 < 4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ‖trace fb (countObservationHolomorphicFilter A hN P h e qs r s hs
        (polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n) d) -
      trace fb (countObservationHolomorphicFilter A hN P h e qs r s hs
        (normalizedCountReconstruction A hN P h e) d)‖ / (4*h+2 : ℝ) ≤
      (2 + 2 * countFilterMajorant A P n *
        majorantConstant ((AsymptoticReconstructedCount.parameters A P).s+4) (4*Real.pi)
          (AsymptoticReconstructedCount.parameters A P).ε) * Real.sqrt (countFilterError A P Y j J n d) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let W := holomorphicSpace (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos
  let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos
  let U := normalizedCountReconstruction A hN P h e
  let V := polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n
  let L := fun i => rowOperator hN (r i) e (hs i) P'.epsilon_pos (P'.s+4) (h+1)
  let b := fun i => rowBound hN (r i) (hs i) P'.epsilon_pos (P'.s+4)
  have hL : ∀ i, ‖L i‖ ≤ b i := fun i => rowOperator_norm_le hN (r i) e (hs i) _ _ _
  have hU : ‖U‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro g
    rw [normalizedCountReconstruction_norm, one_mul]
  have hV : ‖V‖ ≤ 1 := polynomialNormalizedReconstruction_norm_le _
    (scaledCutFiniteCountReconstruction_norm_le A hN P h e Y j J) n
  have hC : 0 ≤ countFilterMajorant A P n :=
    (sq_nonneg _).trans (le_max_left _ _)
  have hbU (l : ℕ) : ‖(⟪countObservationHolomorphicFilter A hN P h e qs r s hs U d (fb l),fb l⟫_ℂ).re‖ ≤
      countFilterMajorant A P n * modeRatio (2*h) (P'.s+4) (4*Real.pi) P'.ε (l+1) := by
    apply (finiteRowFilter_diagonal_bound qs L b hL U hU d W (fb l)).trans
    apply (normalizedCountReconstruction_fourier_gram A hN P h e l).trans
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (modeRatio_nonneg _ _ _ _ P'.epsilon_pos)
  have hbV (l : ℕ) : ‖(⟪countObservationHolomorphicFilter A hN P h e qs r s hs V d (fb l),fb l⟫_ℂ).re‖ ≤
      countFilterMajorant A P n * modeRatio (2*h) (P'.s+4) (4*Real.pi) P'.ε (l+1) := by
    apply (finiteRowFilter_diagonal_bound qs L b hL V hV d W (fb l)).trans
    apply (finiteCountReconstruction_fourier_gram A hN P h e Y j J n l).trans
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (modeRatio_nonneg _ _ _ _ P'.epsilon_pos)
  have herr : ‖countObservationHolomorphicFilter A hN P h e qs r s hs V d -
      countObservationHolomorphicFilter A hN P h e qs r s hs U d‖ ≤ countFilterError A P Y j J n d :=
    (orthogonalCompression_sub_norm_le W _ _).trans
      (observationCylinderFilter_cut_error A hN P h e qs r s hs Y hY j J n d hJ)
  have ht := normalized_trace_sub_le_sqrt_of_absolute_majorants fb _ _ (2*h) (P'.s+4)
    (by positivity : 0 < 4*Real.pi) P'.epsilon_pos hC hD hD1 herr hbV hbU
  convert ht using 1
  push_cast
  ring

#print axioms countObservationHolomorphicFilter_trace_error

end QuantitativeHolomorphic
