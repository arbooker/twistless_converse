module

public import AsymptoticRepeatedObservationsV1
public import AsymptoticRegularStrongTraceV1
public import AsymptoticRegularObservationPositiveFamilyV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Filter ContinuousLinearMap InnerProductSpace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularTrace AsymptoticRegularReconstruction
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)
open scoped InnerProduct Topology ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)
variable {ι : Type*} [Fintype ι]

/-- Repeat each known compact equation (n+1)² times. This changes its
penalty while retaining a finite family of the original observation rows. -/
noncomputable def repeatedPositive (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (n : ℕ) (z : ℍ) : Space →L[ℂ] Space :=
  positive A hN P (fun j : Fin ((n+1)^2) × ι => r j.2)
    (fun j => s j.2) (fun j => hs j.2) e z

noncomputable def jointKernelProjection (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) : Space →L[ℂ] Space :=
  let P' := AsymptoticReconstructedCount.parameters A P
  AsymptoticObservation.kernelProjection (includedExtension A hN P' (multiplier e) z)
    (observations hN r s hs P'.epsilon_pos (P'.s+4) e z)
    (includedExtension_norm_ge A hN P' (multiplier e) z
      (lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)))

theorem repeatedPositive_eq_amplified (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (n : ℕ) (z : ℍ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    repeatedPositive A hN P r s hs e n z=
      AsymptoticObservation.amplified (includedExtension A hN P' (multiplier e) z)
        (observations hN r s hs P'.epsilon_pos (P'.s+4) e z)
        (includedExtension_norm_ge A hN P' (multiplier e) z
          (lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num))) n := by
  dsimp only
  unfold repeatedPositive positive AsymptoticObservation.amplified
  apply AsymptoticObservation.operator_eq_of_gram
  exact AsymptoticObservationStack.repeated_square_gram
    (fun i => AsymptoticRegularObservationRows.row hN (r i) e (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) z) n

theorem repeatedPositive_strong_limit (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) (v : Space) :
    Tendsto (fun n => repeatedPositive A hN P r s hs e n z v) atTop
      (𝓝 (jointKernelProjection A hN P r s hs e z v)) := by
  simp only [repeatedPositive_eq_amplified,jointKernelProjection]
  exact AsymptoticObservation.amplified_tendsto_kernelProjection _ _ _ v

theorem repeatedPositive_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (n : ℕ)
    (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (repeatedPositive A hN P r s hs e n z) a b) :=
  positive_matrix_measurable A hN P _ _ _ e a b

theorem jointKernelProjection_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N)
    (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (jointKernelProjection A hN P r s hs e z) a b) :=
  strong_limit_matrix_measurable _ _ (repeatedPositive_matrix_measurable A hN P r s hs e)
    (repeatedPositive_strong_limit A hN P r s hs e) a b

noncomputable def reconstructionGramRoot (hN : 0<N) (P : Parameters A) (e : Sector N) (z : ℍ) : ℝ≥0∞ :=
  let R := includedFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) z
  ENNReal.ofReal (matrix (R.comp R.adjoint) 1 1).re

omit [Fintype ι] in
theorem reconstructionGramRoot_finite (hN : 0<N) (P : Parameters A) (e : Sector N) :
    ∫⁻ z,reconstructionGramRoot A hN P e z ∂volume≠∞ :=
  (includedFull_range_gram_trace_finite A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e)
    (fun q _ => multiplier_norm e q) (parameters_contraction A hN P (multiplier e)
      (fun q _ => multiplier_norm e q))).ne

theorem repeatedPositive_root_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (n : ℕ) (z : ℍ) :
    ENNReal.ofReal (matrix (repeatedPositive A hN P r s hs e n z) 1 1).re≤
      reconstructionGramRoot A hN P e z := by
  apply ENNReal.ofReal_le_ofReal
  have hg := matrix_gram
    (includedFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) z).adjoint 1
  rw [adjoint_adjoint] at hg
  have he : (matrix (repeatedPositive A hN P r s hs e n z) 1 1).re=
      (⟪repeatedPositive A hN P r s hs e n z (delta 1),delta 1⟫_ℂ).re := by
    rw [matrix,← delta_inner]
    exact inner_re_symm (𝕜:=ℂ) _ _
  exact he.le.trans ((positive_re_inner_le_full_gram A hN P
    (fun j : Fin ((n+1)^2) × ι => r j.2) (fun j => s j.2) (fun j => hs j.2) e z (delta 1)).trans_eq hg.symm)

theorem jointKernelProjection_trace_finite (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    trace volume (jointKernelProjection A hN P r s hs e)<∞ :=
  trace_limit_finite_of_strong_dominated volume _ _
    (repeatedPositive_strong_limit A hN P r s hs e) (reconstructionGramRoot A hN P e)
    (repeatedPositive_root_le A hN P r s hs e) (reconstructionGramRoot_finite A hN P e)

/-- The actual regular finite-observation traces approach the trace of
their joint kernel. The dominating Gram mass is independent of repetition. -/
theorem repeatedPositive_trace_tendsto (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    Tendsto (fun n => (trace volume (repeatedPositive A hN P r s hs e n)).toReal) atTop
      (𝓝 (trace volume (jointKernelProjection A hN P r s hs e)).toReal) :=
  trace_toReal_tendsto_of_strong_dominated volume _ _
    (fun n => repeatedPositive_matrix_measurable A hN P r s hs e n 1 1)
    (repeatedPositive_strong_limit A hN P r s hs e) (reconstructionGramRoot A hN P e)
    (repeatedPositive_root_le A hN P r s hs e) (reconstructionGramRoot_finite A hN P e)

#print axioms repeatedPositive_eq_amplified
#print axioms repeatedPositive_strong_limit
#print axioms repeatedPositive_matrix_measurable
#print axioms jointKernelProjection_matrix_measurable
#print axioms reconstructionGramRoot_finite
#print axioms repeatedPositive_root_le
#print axioms jointKernelProjection_trace_finite
#print axioms repeatedPositive_trace_tendsto

end AsymptoticRegularObservation
