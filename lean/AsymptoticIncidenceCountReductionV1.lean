module

public import AsymptoticUniversalIncidenceTraceV1
public import AsymptoticInfiniteKernelCountReductionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticQuotientIncidence

open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticCongruenceQuotient
open AsymptoticSectorSigns
open scoped ENNReal

theorem space_trace_finite (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (e : Sector N) : trace volume (fun x => (space N hN hε ht e x).starProjection)<∞ := by
  apply projection_trace_finite_of_le volume (space N hN hε ht e) (quotientSpace N hε ht)
    (fun _ => inf_le_left) (projection_trace_finite N hN hε ht)

/-- Sum over the actual closed, unweighted Fricke and ramified incidence
spaces. No classical sector dimension appears in this quantity. -/
noncomputable def totalTrace (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) : ℝ :=
  ∑ e : Sector N,(trace volume (fun x => (space N hN hε ht e x).starProjection)).toReal

#print axioms space_trace_finite

end AsymptoticQuotientIncidence

namespace AsymptoticCompactObservationCount

open UpperHalfPlane MeasureTheory Filter FinitenessCertificate FinitenessGlobalHeight
open AsymptoticSectorSigns AsymptoticSectorComparison Asymptotics FinitenessOriginalInput
open AsymptoticRegularObservation

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The universal original-equation kernel is bounded after summing all
sectors by the unweighted quotient incidence spaces. The positive-weight
removal and finite quotient ambient trace are proved, not assumptions. -/
theorem totalInfiniteKernelTrace_le_incidence (hN : 0<N) (P : Parameters A)
    (K : CompactExhaustion ℍ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    totalInfiniteKernelTrace A hN P (familyRows (universalRows N))
      (familyRegions K) (familyRegions_compact K)≤
        AsymptoticQuotientIncidence.totalTrace N hN P'.epsilon_pos (by omega : 1≤P'.s+4) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  apply Finset.sum_le_sum
  intro e _
  exact ENNReal.toReal_mono
    (AsymptoticQuotientIncidence.space_trace_finite N hN P'.epsilon_pos (by omega : 1≤P'.s+4) e).ne
    (universalKernel_trace_le_incidence A hN P K e)

/-- The analytic part of the requested total-sector strategy, now reduced
to the sharp trace bound for the explicit unweighted incidence spaces
and the two classical TOTAL newspace inputs. These last three hypotheses
remain to be discharged; this is not the completed Theorem 1.2. -/
theorem count_littleO_of_incidence_bound_and_total_dimension
    (hN : 0<N) (P : Parameters A) (K : CompactExhaustion ℍ)
    (c : ℝ) (dimension : ℕ → ℕ)
    (hinc : let P' := AsymptoticReconstructedCount.parameters A P
      AsymptoticQuotientIncidence.totalTrace N hN P'.epsilon_pos (by omega : 1≤P'.s+4)≤
        4*Real.pi*c)
    (hlower : ∀ᶠ k in evenWeights,dimension k≤(S N k).ncard)
    (hdimension : (fun k => (dimension k:ℝ)-c*(k:ℝ))=o[evenWeights] (fun k => (k:ℝ))) :
    (fun k => ((S N k).ncard:ℝ)-(dimension k:ℝ))=o[evenWeights] (fun k => (k:ℝ)) :=
  count_littleO_of_infinite_kernel_bound_and_total_dimension A hN P
    (familyRows (universalRows N)) (familyRegions K) (familyRegions_compact K) c dimension
    ((totalInfiniteKernelTrace_le_incidence A hN P K).trans hinc) hlower hdimension

#print axioms totalInfiniteKernelTrace_le_incidence
#print axioms count_littleO_of_incidence_bound_and_total_dimension

end AsymptoticCompactObservationCount
