module

public import QuantitativeMaassFullBranchExpressionV1
public import QuantitativeMaassFullFilterApproximationV1
public import QuantitativeHolomorphicObservationExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

open ContinuousLinearMap AsymptoticSectorSigns QuantitativeHolomorphic AsymptoticFiniteBranch
open AsymptoticCompactObservationCount Set
namespace QuantitativeMaass.EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- A literal finite rational-branch formula for the full-terminal twist filter. -/
def fullFilterExpression (e : Sector N) {s : Set UpperHalfPlane} (hs : IsCompact s)
    (qs : Finset ℕ+) (n j J d : ℕ) : Expression :=
  observationFilterExpression qs
    (fun q : ℕ+ => rowExpression hN (.twist q.val q.property) e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3))
    (normalizedReconstructionExpression (scaledFullExpression A hN P e j J) n)
    (commonTwistBound A hN P hs) d

theorem fullFilterExpression_eq_ambient (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (n j J d : ℕ) :
    let L := fun q : ℕ+ => rowOperator hN (.twist q.val q.property) e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) 0
    let V := finiteNormalizedReconstruction A hN P e n j J
    holomorphicSum (fullFilterExpression A hN P e hs qs n j J d) 0=
      AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
        ((V.comp ((finiteRowFilter qs L (commonTwistBound A hN P hs) V d).comp V.adjoint)).comp
          AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint) := by
  intro L V
  rw [fullFilterExpression,holomorphicSum_observationFilterExpression,normalizedFullExpression_eq_ambient]
  let S := AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
  let Jc := AsymptoticCylinderLift.lift.toContinuousLinearMap
  let Lh := fun q : ℕ+ => holomorphicSum (rowExpression hN (.twist q.val q.property) e hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+3)) 0
  have hsource := finiteRowFilter_source_transport S
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _) (Jc.comp V) qs Lh
    (commonTwistBound A hN P hs) d
  rw [←comp_assoc]
  apply hsource.trans
  rw [finiteRowFilter_target_transport]
  have hrows : (fun q => (Lh q).comp Jc)=L := by
    funext q
    exact cylinder_rowExpression hN (.twist q.val q.property) e hs _ _ 0
  rw [hrows]

/-- Explicit finite-branch approximation of the actual physical sandwich.
The error is uniform in the sector and in the spectral parameter. -/
theorem fullFilterExpression_ambient_error (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (n j J d : ℕ) (hJ : 0<J) :
    ‖holomorphicSum (fullFilterExpression A hN P e hs qs n j J d) 0-
      (physicalIsometry A hN P e).toContinuousLinearMap.comp
        ((commonResidualFilter A hN P e hs qs d).comp
          (physicalIsometry A hN P e).toContinuousLinearMap.adjoint)‖ ≤
      (2*d+2 : ℝ) *
        (countReconstructionError A P j J*(1+3*(3^n:ℕ))*(7:ℝ)^(4^n)+
          (1-countGramLower A P)^(2^n)/Real.sqrt (countGramLower A P)) := by
  rw [fullFilterExpression_eq_ambient]
  have hh := norm_isometric_transport_difference_le
    AsymptoticCylinderLift.lift.toContinuousLinearMap AsymptoticCylinderLift.lift.adjoint_comp_self
    AsymptoticCylinderLift.lift.toContinuousLinearMap AsymptoticCylinderLift.lift.adjoint_comp_self
    ((finiteNormalizedReconstruction A hN P e n j J).comp
      ((finiteRowFilter qs
        (fun q : ℕ+ => rowOperator hN (.twist q.val q.property) e hs
          (AsymptoticReconstructedCount.parameters A P).epsilon_pos
          ((AsymptoticReconstructedCount.parameters A P).s+3) 0)
        (commonTwistBound A hN P hs) (finiteNormalizedReconstruction A hN P e n j J) d).comp
        (finiteNormalizedReconstruction A hN P e n j J).adjoint))
    ((normalized A hN P e).comp
      ((commonResidualFilter A hN P e hs qs d).comp (normalized A hN P e).adjoint))
  apply le_trans _ (hh.trans (commonResidualFilter_sandwich_finite_error A hN P e hs qs n j J d hJ))
  apply le_of_eq
  congr 1
  change _-((AsymptoticCylinderLift.lift.toContinuousLinearMap.comp (normalized A hN P e)).comp
    ((commonResidualFilter A hN P e hs qs d).comp
      (AsymptoticCylinderLift.lift.toContinuousLinearMap.comp (normalized A hN P e)).adjoint))=_
  rw [adjoint_comp]
  simp only [comp_assoc]

#print axioms fullFilterExpression_eq_ambient
#print axioms fullFilterExpression_ambient_error
end QuantitativeMaass.EulerHilbert.FullTerminal
