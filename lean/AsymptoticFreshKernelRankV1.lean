module

public import AsymptoticFreshGlobalRankV1
public import AsymptoticIntegralKernelsV1
public import AsymptoticInfiniteKernelTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticSectorSigns

/-- A fresh prime uses precisely the sector's untwisted Fricke sign. -/
theorem multiplier_fresh {N q : ℕ} (e : Sector N) (hq : q.Prime) (hf : ¬q∣N) :
    multiplier e q=sign e.1 := by
  have he : q.primeFactors.filter (fun p => p∣N ∧ ¬p^2∣N)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp,hpN,_⟩ := Finset.mem_filter.mp hp
    have hpeq : p=q := (hq.eq_one_or_self_of_dvd p (Nat.mem_primeFactors.mp hp).2.1).resolve_left
      (Nat.mem_primeFactors.mp hp).1.ne_one
    exact hf (hpeq ▸ hpN)
  simp only [multiplier,he,Finset.prod_empty,mul_one]

#print axioms multiplier_fresh

end AsymptoticSectorSigns

namespace AsymptoticFreshKernelRank

open AsymptoticRegularTrace AsymptoticRegularObservation AsymptoticSectorSigns
open AsymptoticFreshRank AsymptoticIntegralSubgroup AsymptoticCornerKernel
open AsymptoticObservationStack AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open FinitenessCertificate FinitenessGlobalHeight UpperHalfPlane MeasureTheory
open AsymptoticCompactObservationCount (Row)
open scoped ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)
variable (q : ℕ) [Fact q.Prime] (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
variable (P : Parameters A) (r : ℕ → Row N) (s : ℕ → Set ℍ)
variable (hs : ∀ i,IsCompact (s i)) (e : Sector N) (K : CompactExhaustion ℍ)

include hqQ

/-- Fresh-prime loss on the literal earlier finite joint kernel used
by the count reduction. All analytic and support hypotheses of the
operator inequality are proved here; only arithmetic freshness remains. -/
theorem finite_prior_loss (n : ℕ) (hf : ∀ i : Fin n,Fresh q (r i)) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let U := finiteKernelSpace A hN P r s hs e n
    let R := fun x => (U x).starProjection
    ((trace volume R).toReal-
      (trace volume (fun x => (globalRemaining (U x) (fun j =>
        stack (observed N q hN hqN (sign e.1) (K.isCompact j)
          P'.epsilon_pos (P'.s+4) R x))).starProjection)).toReal)/(q-1:ℕ)≤
    (trace volume R).toReal-
      (trace volume (fun x => (globalRemaining (U x) (fun j =>
        (row hN (.twist q (Fact.out : q.Prime).pos) e (K.isCompact j)
          P'.epsilon_pos (P'.s+4) x).comp (R x))).starProjection)).toReal := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let U := finiteKernelSpace A hN P r s hs e n
  let R := fun x => (U x).starProjection
  have hm := jointKernelProjection_matrix_measurable A hN P
    (fun i : Fin n => r i) (fun i => s i) (fun i => hs i) e
  have hc := jointKernelProjection_covariant A hN P
    (fun i : Fin n => r i) (fun i => s i) (fun i => hs i) e
  have hi := jointKernelProjection_supported q A hN hqN hqQ P
    (fun i : Fin n => r i) hf (fun i => s i) (fun i => hs i) e
  have ht := jointKernelProjection_trace_finite A hN P
    (fun i : Fin n => r i) (fun i => s i) (fun i => hs i) e
  have he := AsymptoticFreshRank.global_rank_loss N q hN hqN (sign e.1) K
    P'.epsilon_pos (P'.s+4) U (hm 1 1) R hm hc hi
    (fun x => (U x).isIdempotentElem_starProjection) 1 zero_le_one
    (fun x => (U x).starProjection_norm_le) ht
  simpa only [AsymptoticRegularObservationRows.row,
    multiplier_fresh e (Fact.out : q.Prime) hqN] using he

/-- Earlier global equation families are allowed as well, provided
their moduli all avoid the new prime. -/
theorem infinite_prior_loss (hf : ∀ i,Fresh q (r i)) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let U := infiniteKernelSpace A hN P r s hs e
    let R := fun x => (U x).starProjection
    ((trace volume R).toReal-
      (trace volume (fun x => (globalRemaining (U x) (fun j =>
        stack (observed N q hN hqN (sign e.1) (K.isCompact j)
          P'.epsilon_pos (P'.s+4) R x))).starProjection)).toReal)/(q-1:ℕ)≤
    (trace volume R).toReal-
      (trace volume (fun x => (globalRemaining (U x) (fun j =>
        (row hN (.twist q (Fact.out : q.Prime).pos) e (K.isCompact j)
          P'.epsilon_pos (P'.s+4) x).comp (R x))).starProjection)).toReal := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let U := infiniteKernelSpace A hN P r s hs e
  let R := fun x => (U x).starProjection
  have hm := infiniteKernelProjection_matrix_measurable A hN P r s hs e
  have hc := infiniteKernelProjection_covariant A hN P r s hs e
  have hi := infiniteKernelProjection_supported q A hN hqN hqQ P r hf s hs e
  have ht := infiniteKernelProjection_trace_finite A hN P r s hs e
  have he := AsymptoticFreshRank.global_rank_loss N q hN hqN (sign e.1) K
    P'.epsilon_pos (P'.s+4) U (hm 1 1) R hm hc hi
    (fun x => (U x).isIdempotentElem_starProjection) 1 zero_le_one
    (fun x => (U x).starProjection_norm_le) ht
  simpa only [AsymptoticRegularObservationRows.row,
    multiplier_fresh e (Fact.out : q.Prime) hqN] using he

#print axioms finite_prior_loss
#print axioms infinite_prior_loss

end AsymptoticFreshKernelRank
