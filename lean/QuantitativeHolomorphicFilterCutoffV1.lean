module

public import QuantitativeHolomorphicFilterComparisonV1
public import QuantitativeHolomorphicSectorFilterTraceV1
public import AsymptoticCylinderUpperCutoffV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticObservation AsymptoticCompactObservationCount
open AsymptoticDiagonalTrace AsymptoticFiniteBranch AsymptoticCylinderModeComparison AsymptoticFourierNorm

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

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable {ι : Type*}

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
    let B := (4 : ℝ)^(4^n)
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
    let B := (4 : ℝ)^(4^n)
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

#print axioms finiteFilter_upperCut_explicit_error

#print axioms finiteNormalizedCount_left_height
#print axioms finiteFilter_upperCut_trace_error

end QuantitativeHolomorphic
