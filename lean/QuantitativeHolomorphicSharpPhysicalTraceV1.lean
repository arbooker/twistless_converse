module

public import QuantitativeHolomorphicSharpMajorantV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Sharp

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation AsymptoticCompactObservationCount
open AsymptoticDiagonalTrace InnerProductSpace AsymptoticFiniteBranch AsymptoticCylinderModeComparison
open scoped InnerProduct

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

def countFilterMajorant (P : Parameters A) (n : ℕ) : ℝ :=
  max (((Real.sqrt (countGramLower A P))⁻¹)^2) (((3/2:ℝ)^n)^2)

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

private theorem retained_sandwich_of_lower_support {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (V : G →L[ℂ] Space) (F : G →L[ℂ] G) (Y H : ℝ)
    (hV : (upperProjection Y).comp V = V) (W : Submodule ℂ Space) [CompleteSpace W] :
    compressedSandwich (retainedProjection Y H) (V.comp (F.comp V.adjoint)) W =
      compressedSandwich (removePart (upperProjection H) V) F W := by
  have hp : (retainedProjection Y H).comp V = removePart (upperProjection H) V := by
    rw [retainedProjection, comp_assoc, hV]
    ext1 x
    simp [removePart]
  rw [← hp]
  simp only [compressedSandwich, adjoint_comp, retainedProjection_adjoint, comp_assoc]

theorem upperCompression_trace_le_massBound (m t : ℕ) {scale ε H : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) (hH : 0 < H) :
    trace (fourierBasis m t hs hε) (upperCompression m t hs hε H) ≤ massBound m t scale H := by
  simp only [trace, upperCompression_diagonal, massBound]
  exact (upperMass_summable_bound m t hs hε hH).2

private theorem upperCutError_mono_right (A B C : ℝ) (hC : 0 ≤ C) {r r' : ℝ} (hr : r ≤ r') :
    upperCutError A B C r ≤ upperCutError A B C r' := by
  unfold upperCutError
  gcongr

theorem finiteNormalizedCount_left_height (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (Y : ℝ) (j J n : ℕ) :
    (upperProjection Y).comp
      (polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n) =
        polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n := by
  rw [polynomialNormalizedReconstruction, ← comp_assoc]
  have hv : (upperProjection Y).comp (scaledCutFiniteCountReconstruction A hN P h e Y j J) =
      scaledCutFiniteCountReconstruction A hN P h e Y j J := by
    rw [scaledCutFiniteCountReconstruction, comp_smul, finiteCutReconstruction_left_height]
  rw [hv]

/-- Every upper-height cutoff is explicit.  The bound uses the actual
Fourier cusp mass rather than a qualitative eventual choice of height. -/
theorem finiteFilter_upperCut_trace_error (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (Y H : ℝ) (hH : 0 < H) (j J n d : ℕ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos
    let B := (3/2:ℝ)^n
    ‖trace fb (countObservationHolomorphicFilter A hN P h e qs r s hs
        (polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n) d) -
      finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d (P'.s+4)‖ / (2*h+2 : ℝ) ≤
      upperCutError (B^2 * (1 + majorantConstant (P'.s+4) (4*Real.pi) P'.ε)) B 1
        (trace fb (upperCompression (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos H) /
          (2*h+2 : ℝ)) := by
  dsimp only
  let P' := AsymptoticReconstructedCount.parameters A P
  let W := holomorphicSpace (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos
  let V := polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n
  let R := finiteCountWeightedNormalizer A hN P h e Y j J n
  let L := fun i => rowOperator hN (r i) e (hs i) P'.epsilon_pos (P'.s+4) (h+1)
  let b := fun i => rowBound hN (r i) (hs i) P'.epsilon_pos (P'.s+4)
  let F := finiteRowFilter qs L b V d
  have hV : ‖V‖ ≤ 1 := polynomialNormalizedReconstruction_norm_le _
    (scaledCutFiniteCountReconstruction_norm_le A hN P h e Y j J) n
  have hF : ‖F‖ ≤ 1 := (finiteRowFilter_order qs L b
    (fun i => rowOperator_norm_le hN (r i) e (hs i) _ _ _) V hV d).2.2
  have ht := factored_upperCut_trace_bound R F (finiteCountWeightedNormalizer_norm_le A hN P h e Y j J n)
    hF (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos hH
  have hv : (inclusion P'.epsilon_pos).comp R = V :=
    (finiteCountReconstruction_weighted A hN P h e Y j J n).symm
  rw [hv] at ht
  have hr := retained_sandwich_of_lower_support V F Y H
    (finiteNormalizedCount_left_height A hN P h e Y j J n) W
  have he : finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d (P'.s+4) =
      upperCutTrace V F (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos H :=
    congrArg (trace (fourierBasis (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos)) hr
  have hfull : countObservationHolomorphicFilter A hN P h e qs r s hs V d =
      compressedSandwich V F W := rfl
  rw [he, hfull]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using ht

/-- Explicit height/depth version: the upper cusp mass is replaced by its
proved elementary bound, so no trace quantity remains in the error. -/
theorem finiteFilter_upperCut_explicit_error (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (Y H : ℝ) (hH : 0 < H) (j J n d : ℕ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0 < 4*Real.pi) P'.epsilon_pos
    let B := (3/2:ℝ)^n
    ‖trace fb (countObservationHolomorphicFilter A hN P h e qs r s hs
        (polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n) d) -
      finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d (P'.s+4)‖ / (2*h+2 : ℝ) ≤
      upperCutError (B^2 * (1 + majorantConstant (P'.s+4) (4*Real.pi) P'.ε)) B 1
        (massBound (2*h) (P'.s+4) (4*Real.pi) H / (2*h+2 : ℝ)) := by
  apply (finiteFilter_upperCut_trace_error A hN P h e qs r s hs Y H hH j J n d).trans
  apply upperCutError_mono_right _ _ _ zero_le_one
  exact div_le_div_of_nonneg_right
    (upperCompression_trace_le_massBound (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4)
      (by positivity : 0 < 4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos hH) (by positivity)

#print axioms countObservationHolomorphicFilter_trace_error
#print axioms sector_finrank_le_finite_filter_trace
#print axioms finiteFilter_upperCut_explicit_error

end QuantitativeHolomorphic.Sharp
