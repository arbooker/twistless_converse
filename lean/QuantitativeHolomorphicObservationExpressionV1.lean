module

public import QuantitativeHolomorphicNewtonTransportV1
public import QuantitativeHolomorphicFilterTransportV1
public import QuantitativeHolomorphicFilterExpressionV1
public import QuantitativeHolomorphicObservationApproximationV1
public import AsymptoticFiniteBranchRowsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open ContinuousLinearMap AsymptoticCompactObservationCount AsymptoticFiniteBranch

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable {ι : Type*}

/-- A common finite rational-branch expression for the actual compact
holomorphic global filter.  The expression is independent of the weight. -/
def countObservationFilterExpression (hN : 0 < N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (Y : ℝ) (j J n d : ℕ) : Expression :=
  observationFilterExpression qs
    (fun i => rowExpression hN (r i) e (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4))
    (normalizedReconstructionExpression (scaledCutCountExpression A hN P e Y j J) n)
    (fun i => rowBound hN (r i) (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4)) d

/-- Exact realization on the cylinder: source-coordinate complements cancel
inside the sandwich, rather than being discarded from the polynomial. -/
theorem holomorphicSum_countObservationFilterExpression (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (Y : ℝ) (j J n d : ℕ) :
    holomorphicSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) (h+1) =
      AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
        ((observationCylinderFilter A hN P h e qs r s hs
          (polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n) d).comp
          AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint) := by
  rw [countObservationFilterExpression, holomorphicSum_observationFilterExpression,
    holomorphicSum_normalizedCutCountExpression]
  let S := AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
  let Jc := AsymptoticCylinderLift.lift.toContinuousLinearMap
  let V := polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n
  let L := fun i => holomorphicSum (rowExpression hN (r i) e (hs i)
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4)) (h+1)
  let b := fun i => rowBound hN (r i) (hs i)
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4)
  have hsource := finiteRowFilter_source_transport S
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _) (Jc.comp V) qs L b d
  rw [← comp_assoc]
  apply hsource.trans
  rw [finiteRowFilter_target_transport]
  have hrows : (fun i => (L i).comp Jc) = fun i => rowOperator hN (r i) e (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) (h+1) := by
    funext i
    exact cylinder_rowExpression hN (r i) e (hs i) _ _ _
  rw [hrows]
  rfl

/-- Explicit actual finite-branch approximation of the exact ambient positive
observation filter.  No geometry or trace assumption is used in this norm bound. -/
theorem countObservationFilterExpression_ambient_error (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (Y : ℝ) (hY : 0 ≤ Y) (j J n d : ℕ) (hJ : 0 < J) :
    ‖holomorphicSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) (h+1) -
      AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
        ((observationCylinderFilter A hN P h e qs r s hs
          (normalizedCountReconstruction A hN P h e) d).comp
          AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint)‖ ≤
      (2 * d + 2 : ℝ) * normalizedCutError A P Y j J n := by
  rw [holomorphicSum_countObservationFilterExpression]
  exact (norm_isometric_transport_difference_le _ AsymptoticCylinderLift.lift.adjoint_comp_self
    _ AsymptoticCylinderLift.lift.adjoint_comp_self _ _).trans
    (observationCylinderFilter_cut_error A hN P h e qs r s hs Y hY j J n d hJ)

#print axioms holomorphicSum_countObservationFilterExpression
#print axioms countObservationFilterExpression_ambient_error

end QuantitativeHolomorphic
