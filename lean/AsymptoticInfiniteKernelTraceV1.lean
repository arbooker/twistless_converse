module

public import AsymptoticRegularInfiniteKernelV1
public import AsymptoticProjectionTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularTrace
open AsymptoticCompactObservationCount (Row)
open scoped ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem infiniteKernelSpace_le_finite (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (n : ℕ) (z : ℍ) :
    infiniteKernelSpace A hN P r s hs e z≤finiteKernelSpace A hN P r s hs e n z := by
  rw [infiniteKernelSpace_eq_iInf]
  exact iInf_le _ n

/-- The full joint kernel has finite trace; taking its real value does
not discard an infinite value. It is dominated by every finite prefix. -/
theorem infiniteKernelProjection_trace_le_finite (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (n : ℕ) :
    trace volume (infiniteKernelProjection A hN P r s hs e)≤
      trace volume (jointKernelProjection A hN P
        (fun i : Fin n => r i) (fun i => s i) (fun i => hs i) e) := by
  have ht := projection_trace_mono volume (infiniteKernelSpace A hN P r s hs e)
    (finiteKernelSpace A hN P r s hs e n) (infiniteKernelSpace_le_finite A hN P r s hs e n)
  unfold infiniteKernelProjection
  simpa only [finiteKernelProjection_eq] using ht

theorem infiniteKernelProjection_trace_finite (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    trace volume (infiniteKernelProjection A hN P r s hs e)<∞ :=
  (infiniteKernelProjection_trace_le_finite A hN P r s hs e 0).trans_lt
    (jointKernelProjection_trace_finite A hN P
      (fun i : Fin 0 => r i) (fun i => s i) (fun i => hs i) e)

#print axioms infiniteKernelSpace_le_finite
#print axioms infiniteKernelProjection_trace_le_finite
#print axioms infiniteKernelProjection_trace_finite

end AsymptoticRegularObservation
