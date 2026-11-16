module

public import QuantitativeMaassFullResidualFilterV1
public import QuantitativeMaassFullFiniteNormalizationV1
public import QuantitativeHolomorphicFilterStabilityV1
public import QuantitativeHolomorphicSimultaneousCutoffsV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap AsymptoticSectorSigns QuantitativeHolomorphic
open AsymptoticCompactObservationCount Set

namespace QuantitativeMaass.EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

theorem normalized_operator_norm (e : Sector N) : ‖normalized A hN P e‖≤1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  rw [normalized_norm, one_mul]

/-- The common filter is the literal weight-zero row filter on the
normalized full terminal space. -/
theorem commonResidualFilter_eq (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) :
    commonResidualFilter A hN P e hs qs d =
      finiteRowFilter qs
        (fun q : ℕ+ => rowOperator hN (.twist q.val q.property) e hs
          (AsymptoticReconstructedCount.parameters A P).epsilon_pos
          ((AsymptoticReconstructedCount.parameters A P).s+3) 0)
        (commonTwistBound A hN P hs) (normalized A hN P e) d := rfl

/-- Replacing reconstruction by its finite polynomial costs only the
degree times the explicit reconstruction error; row counts and norms are
already paid by the common normalization. -/
theorem commonResidualFilter_finite_error (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (n j J d : ℕ) (hJ : 0<J) :
    ‖finiteRowFilter qs
      (fun q : ℕ+ => rowOperator hN (.twist q.val q.property) e hs
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+3) 0)
      (commonTwistBound A hN P hs) (finiteNormalizedReconstruction A hN P e n j J) d -
      commonResidualFilter A hN P e hs qs d‖ ≤
      (2*d : ℝ) *
        (countReconstructionError A P j J*(1+3*(3^n:ℕ))*(7:ℝ)^(4^n)+
          (1-countGramLower A P)^(2^n)/Real.sqrt (countGramLower A P)) := by
  rw [commonResidualFilter_eq]
  apply (finiteRowFilter_difference qs _ _
    (fun q => rowOperator_norm_le hN (.twist q.val q.property) e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) 0)
    (normalized A hN P e) (finiteNormalizedReconstruction A hN P e n j J)
    (normalized_operator_norm A hN P e)
    (finiteNormalizedReconstruction_norm A hN P e n j J) d).trans
  exact mul_le_mul_of_nonneg_left (finiteNormalizedReconstruction_error A hN P e n j J hJ)
    (by positivity)

/-- The same degree-linear error holds after placing reconstruction on both
sides, as required for the physical trace comparison. -/
theorem commonResidualFilter_sandwich_finite_error (e : Sector N)
    {s : Set UpperHalfPlane} (hs : IsCompact s) (qs : Finset ℕ+)
    (n j J d : ℕ) (hJ : 0<J) :
    let L := fun q : ℕ+ => rowOperator hN (.twist q.val q.property) e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) 0
    let V := finiteNormalizedReconstruction A hN P e n j J
    let U := normalized A hN P e
    ‖V.comp ((finiteRowFilter qs L (commonTwistBound A hN P hs) V d).comp V.adjoint)-
      U.comp ((commonResidualFilter A hN P e hs qs d).comp U.adjoint)‖ ≤
      (2*d+2 : ℝ) *
        (countReconstructionError A P j J*(1+3*(3^n:ℕ))*(7:ℝ)^(4^n)+
          (1-countGramLower A P)^(2^n)/Real.sqrt (countGramLower A P)) := by
  intro L V U
  rw [commonResidualFilter_eq]
  apply (finiteRowFilter_sandwich_difference qs L _
    (fun q => rowOperator_norm_le hN (.twist q.val q.property) e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) 0) U V
    (normalized_operator_norm A hN P e)
    (finiteNormalizedReconstruction_norm A hN P e n j J) d).trans
  exact mul_le_mul_of_nonneg_left (finiteNormalizedReconstruction_error A hN P e n j J hJ)
    (by positivity)

/-- The existing explicit cutoff schedule pays the actual weight-zero
sandwich error at every prescribed positive accuracy. -/
theorem commonResidualFilter_scheduled_error (e : Sector N)
    {s : Set UpperHalfPlane} (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ)
    {δ : ℝ} (hδ : 0<δ) :
    let D : ℝ := 2*d+2
    let n := Schedule.newtonDepth A P D δ
    let j := Schedule.reconstructionDepth A P D δ n
    let J := Schedule.foldCutoff A P D δ j n
    let L := fun q : ℕ+ => rowOperator hN (.twist q.val q.property) e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) 0
    let V := finiteNormalizedReconstruction A hN P e n j J
    let U := normalized A hN P e
    0<J ∧ ‖V.comp ((finiteRowFilter qs L (commonTwistBound A hN P hs) V d).comp V.adjoint)-
      U.comp ((commonResidualFilter A hN P e hs qs d).comp U.adjoint)‖ ≤ δ := by
  intro D n j J L V U
  let Y := Schedule.lowerCutoff A P D δ n
  have h := Schedule.countFilterError_schedule A P d hδ
  change 0<J ∧ 0<Y ∧ 0<countFilterError A P Y j J n d ∧
    countFilterError A P Y j J n d≤δ at h
  refine ⟨h.1, ?_⟩
  have he := commonResidualFilter_sandwich_finite_error A hN P e hs qs n j J d h.1
  apply he.trans
  apply le_trans _ h.2.2.2
  unfold countFilterError normalizedCutError cutCountReconstructionError
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply le_add_of_nonneg_right
  exact mul_nonneg
    (div_nonneg h.2.1.le (AsymptoticReconstructedCount.parameters A P).epsilon_pos.le)
    (zero_le_one.trans (countReconstructionBound_one_le A P))

#print axioms normalized_operator_norm
#print axioms commonResidualFilter_eq
#print axioms commonResidualFilter_finite_error
#print axioms commonResidualFilter_sandwich_finite_error
#print axioms commonResidualFilter_scheduled_error

end QuantitativeMaass.EulerHilbert.FullTerminal
