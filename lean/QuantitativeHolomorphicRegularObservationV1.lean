module

public import QuantitativeHolomorphicObservationExpressionV1
public import QuantitativeHolomorphicRegularNewtonTransportV1
public import QuantitativeHolomorphicCommonRowBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open ContinuousLinearMap AsymptoticCompactObservationCount AsymptoticFiniteBranch

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable {ι : Type*}

def observationRegularFilter (hN : 0 < N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (z : UpperHalfPlane)
    (V : (AsymptoticRegularReconstruction.TerminalSpace A
        (AsymptoticReconstructedCount.parameters A P) z) →L[ℂ] AsymptoticRegularFoldedLow.Space) (d : ℕ) :=
  let L := fun i => AsymptoticRegularObservationRows.row hN (r i) e (hs i)
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4) z
  let b := fun i => rowBound hN (r i) (hs i)
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4)
  V.comp ((finiteRowFilter qs L b V d).comp V.adjoint)

/-- The exact same rational expression represents the finite regular filter,
with the same observation normalization and polynomial degrees. -/
theorem regularSum_countObservationFilterExpression (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (z : UpperHalfPlane) (Y : ℝ) (j J n d : ℕ) :
    regularSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) z =
      observationRegularFilter A hN P e qs r s hs z
        (polynomialNormalizedReconstruction (scaledCutFiniteRegularCountReconstruction A hN P e z Y j J) n) d := by
  let S := (AsymptoticRegularReconstruction.TerminalSpace A
    (AsymptoticReconstructedCount.parameters A P) z).subtypeL
  have hS : S.adjoint.comp S = 1 :=
    AsymptoticOrbitRegion.adjoint_comp_subtype (G := AsymptoticRationalGroup.Group)
      (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z
  let V := polynomialNormalizedReconstruction (scaledCutFiniteRegularCountReconstruction A hN P e z Y j J) n
  let rows := fun i => rowExpression hN (r i) e (hs i)
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4)
  let b := fun i => rowBound hN (r i) (hs i)
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4)
  have he := regularSum_observationFilterExpression qs rows
    (normalizedReconstructionExpression (scaledCutCountExpression A hN P e Y j J) n) b d z
  have hv := regularSum_normalizedCutCountExpression A hN P e z n Y j J
  have hh := congrArg (fun W : RegularSpace →L[ℂ] RegularSpace =>
    W.comp ((finiteRowFilter qs (fun i => regularSum (rows i) z) b W d).comp W.adjoint)) hv
  have hsource := finiteRowFilter_source_transport S hS V qs
    (fun i => regularSum (rows i) z) b d
  have hr : (fun i => regularSum (rows i) z) = fun i =>
      AsymptoticRegularObservationRows.row hN (r i) e (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) z := by
    funext i
    exact regularSum_rowExpression hN (r i) e (hs i) _ _ z
  have hfinal := congrArg (fun L : ι → RegularSpace →L[ℂ] RegularSpace =>
    V.comp ((finiteRowFilter qs L b V d).comp V.adjoint)) hr
  exact he.trans (hh.trans (hsource.trans hfinal))

/-- Uniform operator error in every regular orbit fiber, with the same
explicit right side as the physical filter approximation. -/
theorem countObservationFilterExpression_regular_error (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (z : UpperHalfPlane) (Y : ℝ) (hY : 0 ≤ Y)
    (j J n d : ℕ) (hJ : 0 < J) :
    ‖regularSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) z -
      observationRegularFilter A hN P e qs r s hs z
        (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d‖ ≤
      (2 * d + 2 : ℝ) * normalizedCutError A P Y j J n := by
  rw [regularSum_countObservationFilterExpression]
  let U := normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)
  let V := polynomialNormalizedReconstruction (scaledCutFiniteRegularCountReconstruction A hN P e z Y j J) n
  have hU : ‖U‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro g
    rw [normalizedRegularCountReconstruction_norm, one_mul]
  have hV : ‖V‖ ≤ 1 := polynomialNormalizedReconstruction_norm_le _
    (scaledCutFiniteRegularCountReconstruction_norm_le A hN P e z Y j J) n
  have hd := cut_normalizedRegularCountReconstruction_closed_error A hN P e z n Y hY j J hJ
  exact (finiteRowFilter_sandwich_difference qs _ _
    (fun i => regular_row_norm_le_physical_bound hN (r i) e (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) z) U V hU hV d).trans
      (mul_le_mul_of_nonneg_left hd (by positivity))

#print axioms regularSum_countObservationFilterExpression
#print axioms countObservationFilterExpression_regular_error

end QuantitativeHolomorphic
