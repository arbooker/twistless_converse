module

public import AsymptoticUniversalIncidenceTransportV1
public import AsymptoticRegularIntersectionV1
public import AsymptoticCongruenceTraceFiniteV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory AsymptoticCongruenceQuotient AsymptoticRegularTrace
open AsymptoticSubspaceIntersection AsymptoticCompactObservationCount AsymptoticSectorSigns
open FinitenessCertificate FinitenessGlobalHeight
open scoped ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The full Euler kernel has trace at most that of the actual unweighted
incidence space. Coordinate transport, almost-everywhere quotient inclusion
and finiteness of the quotient ambient trace are all proved inputs. -/
theorem universalKernel_trace_le_incidence (hN : 0<N) (P : Parameters A)
    (K : CompactExhaustion ℍ) (e : Sector N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    trace volume (fun x => (globalKernelSpace A hN P (universalRows N) K e x).starProjection)≤
      trace volume (fun x => (AsymptoticQuotientIncidence.space N hN
        P'.epsilon_pos (by omega : 1≤P'.s+4) e x).starProjection) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let U := globalKernelSpace A hN P (universalRows N) K e
  let V := quotientSpace N P'.epsilon_pos (by omega : 1≤P'.s+4)
  let W := fun x => inter (U x) (V x)
  have hreg := inter_regular U V
    (globalKernelProjection_matrix_measurable A hN P (universalRows N) K e)
    (projection_matrix_measurable N P'.epsilon_pos (by omega))
    (globalKernelProjection_covariant A hN P (universalRows N) K e)
    (projection_covariant N P'.epsilon_pos (by omega))
  have heq : trace volume (fun x => (W x).starProjection)=
      trace volume (fun x => (U x).starProjection) :=
    trace_inter_eq_of_ae_le volume U V (universalKernel_ae_quotient_range A hN P K e)
  change trace volume (fun x => (U x).starProjection)≤_
  rw [← heq]
  refine trace_le_of_normalized_transport N P'.epsilon_pos (by omega) W
    (AsymptoticQuotientIncidence.space N hN P'.epsilon_pos (by omega : 1≤P'.s+4) e)
    ?_ hreg.1 hreg.2 (projection_trace_finite N hN P'.epsilon_pos (by omega : 1≤P'.s+4)) ?_
  · intro x u hu
    exact ((inter_mem (U x) (V x) u).mp hu).2
  · intro x u v hu hv
    have hm := (inter_mem (U x) (V x) u).mp hu
    exact universalKernel_normalized_transport A hN P K e x u v hm.1 hm.2 hv

#print axioms universalKernel_trace_le_incidence

end AsymptoticRegularObservation
