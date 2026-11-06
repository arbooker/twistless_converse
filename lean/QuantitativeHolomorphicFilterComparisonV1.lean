module

public import QuantitativeHolomorphicRegularObservationV1
public import QuantitativeHolomorphicUniformTraceV1
public import AsymptoticRetainedWeightedLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticObservation AsymptoticCompactObservationCount
open AsymptoticDiagonalTrace AsymptoticFiniteBranch AsymptoticRegularTrace
open AsymptoticUnweightedKernel AsymptoticCylinderModeComparison MeasureTheory

/-- Quantitative weighted/unweighted replacement, before any asymptotic
parameter choice.  The upper endpoint does not enter this bound. -/
theorem retained_weighted_trace_difference (m t : ℕ) {ε Y : ℝ}
    (hε : 0 < ε) (hY : 0 < Y) (H : ℝ) (W : Space →L[ℂ] Space) (hW : ‖W‖ ≤ 1) :
    ‖(trace (fourierBasis m t (by positivity : 0 < 4*Real.pi) hε)
        (compressedSandwich (retainedProjection Y H) W
          (holomorphicSpace m t (by positivity : 0 < 4*Real.pi) hε)) -
      trace (fourierBasis m 0 (by positivity : 0 < 4*Real.pi) hε)
        (compressedSandwich (retainedProjection Y H) W
          (holomorphicSpace m 0 (by positivity : 0 < 4*Real.pi) hε))) / (m+2 : ℝ)‖ ≤
      (2 * Real.sqrt (localizedErrorBound t (4*Real.pi) Y) *
        Real.sqrt (massSlope t (4*Real.pi) Y)) * (Real.sqrt (m+2 : ℝ))⁻¹ := by
  rw [retained_trace_eq_localized, retained_trace_eq_localized]
  simpa only [mul_one] using normalized_localizedTrace_difference_bound m t
    (by positivity : 0 < 4*Real.pi) hε hY _ ((retained_sandwich_norm_le Y H W).trans hW)

private theorem contraction_sandwich_norm_le {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : G →L[ℂ] H) (F : G →L[ℂ] G) (hV : ‖V‖ ≤ 1) (hF : ‖F‖ ≤ 1) :
    ‖V.comp (F.comp V.adjoint)‖ ≤ 1 := by
  have ha : ‖V.adjoint‖ ≤ 1 := by rwa [adjoint.norm_map]
  have hi : ‖F.comp V.adjoint‖ ≤ 1 := by
    exact (opNorm_comp_le _ _).trans (by simpa only [one_mul] using mul_le_mul hF ha (norm_nonneg _) zero_le_one)
  exact (opNorm_comp_le _ _).trans (by simpa only [one_mul] using mul_le_mul hV hi (norm_nonneg _) zero_le_one)

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable {ι : Type*}

theorem observationCylinderFilter_norm_le (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (V : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε →L[ℂ] Space)
    (hV : ‖V‖ ≤ 1) (d : ℕ) : ‖observationCylinderFilter A hN P h e qs r s hs V d‖ ≤ 1 :=
  contraction_sandwich_norm_le V _ hV (finiteRowFilter_order qs _ _
    (fun i => rowOperator_norm_le hN (r i) e (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) (h+1)) V hV d).2.2

def finiteRetainedFilterTrace (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (Y H : ℝ) (j J n d t : ℕ) : ℝ :=
  trace (fourierBasis (2*h) t (by positivity : 0 < 4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos)
    (compressedSandwich (retainedProjection Y H)
      (observationCylinderFilter A hN P h e qs r s hs
        (polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n) d)
      (holomorphicSpace (2*h) t (by positivity : 0 < 4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos))

theorem retained_countFilter_liftedTrace (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (Y H : ℝ) (j J n d : ℕ) :
    liftedTrace h (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      (holomorphicSum (retainedExpression Y H
        (countObservationFilterExpression A hN P e qs r s hs Y j J n d)) (h+1)) =
      finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d 0 := by
  rw [holomorphicSum_retainedExpression, holomorphic_corner, holomorphicSum_countObservationFilterExpression]
  exact retained_lift_trace h _ Y H _

/-- The actual weighted finite-filter trace is compared to its actual
retained regular trace.  The only nonnumeric input is the explicit integer
matrix geometry of its finite branch list, not a trace or convergence premise. -/
theorem finiteRetainedFilterTrace_regular_comparison (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (Y H D : ℝ) (hY : 0 < Y) (hH : 0 < H) (hD : 0 ≤ D) (j J n d : ℕ)
    (S : Finset ℤ) (hsmall : (h+1 : ℝ)^(-(1/3 : ℝ))*D ≤ 1)
    (hfar : ∀ a : ℤ, a ∉ S → 2 * compactBaseBound Y H 1 ≤ 1 + |(a : ℝ)|)
    (geom : ∀ b ∈ countObservationFilterExpression A hN P e qs r s hs Y j J n d,
      b.label ≠ 1 → RetainedBranchGeometry b Y H D S) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let E := countObservationFilterExpression A hN P e qs r s hs Y j J n d
    |finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d (P'.s+4) / (2*h+2 : ℝ) -
      signedTrace volume (fun z => (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        ((observationRegularFilter A hN P e qs r s hs z
          (polynomialNormalizedReconstruction (scaledCutFiniteRegularCountReconstruction A hN P e z Y j J) n) d).comp
          (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z))) / (4*Real.pi)| ≤
      (2 * Real.sqrt (localizedErrorBound (P'.s+4) (4*Real.pi) Y) *
        Real.sqrt (massSlope (P'.s+4) (4*Real.pi) Y)) * (Real.sqrt (2*h+2 : ℝ))⁻¹ +
      (expressionBound E + (E.length : ℝ)) * uniformRetainedTraceError D Y H h S.card := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let E := countObservationFilterExpression A hN P e qs r s hs Y j J n d
  let V := polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n
  have hV : ‖V‖ ≤ 1 := polynomialNormalizedReconstruction_norm_le _
    (scaledCutFiniteCountReconstruction_norm_le A hN P h e Y j J) n
  have hw := retained_weighted_trace_difference (2*h) (P'.s+4) P'.epsilon_pos hY H
    (observationCylinderFilter A hN P h e qs r s hs V d)
    (observationCylinderFilter_norm_le A hN P h e qs r s hs V hV d)
  have hb := retained_expression_uniform_trace_bound E P'.epsilon_pos hD hY hH h hsmall S hfar geom
  rw [retained_countFilter_liftedTrace] at hb
  have hre : regularSum (retainedExpression Y H E) = fun z =>
      (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        ((observationRegularFilter A hN P e qs r s hs z
          (polynomialNormalizedReconstruction (scaledCutFiniteRegularCountReconstruction A hN P e z Y j J) n) d).comp
          (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)) := by
    funext z
    exact (regularSum_retainedExpression Y H E z).trans
      (congrArg (fun T : RegularSpace →L[ℂ] RegularSpace =>
        (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
          (T.comp (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)))
        (regularSum_countObservationFilterExpression A hN P e qs r s hs z Y j J n d))
  rw [hre] at hb
  have hw' : |finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d (P'.s+4) / (2*h+2 : ℝ) -
      finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d 0 / (2*h+2 : ℝ)| ≤
      (2 * Real.sqrt (localizedErrorBound (P'.s+4) (4*Real.pi) Y) *
        Real.sqrt (massSlope (P'.s+4) (4*Real.pi) Y)) * (Real.sqrt (2*h+2 : ℝ))⁻¹ := by
    simpa only [finiteRetainedFilterTrace, Nat.cast_mul, Nat.cast_ofNat, Real.norm_eq_abs, sub_div] using hw
  apply (abs_sub_le _ (finiteRetainedFilterTrace A hN P h e qs r s hs Y H j J n d 0 / (2*h+2 : ℝ)) _).trans
  apply add_le_add hw'
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hb

#print axioms finiteRetainedFilterTrace_regular_comparison

end QuantitativeHolomorphic
