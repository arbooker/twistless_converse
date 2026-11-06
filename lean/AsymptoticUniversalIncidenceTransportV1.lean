module

public import AsymptoticQuotientIncidenceSpaceV1
public import AsymptoticUniversalQuotientKernelV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory AsymptoticCongruenceQuotient
open AsymptoticCompactObservationCount AsymptoticSectorSigns
open FinitenessCertificate FinitenessGlobalHeight
open AsymptoticRegularCompactBranch (Space)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Multiplication by the actual inverse square-root weight takes every
square-summable image of an original Euler-kernel vector to the closed
unweighted Fricke and ramified incidence space. The multiplier itself
need not be bounded on the whole Hilbert space. -/
theorem universalKernel_normalized_transport (hN : 0<N) (P : Parameters A)
    (K : CompactExhaustion ℍ) (e : Sector N) (x : ℍ) (u v : Space)
    (hu : u∈globalKernelSpace A hN P (universalRows N) K e x)
    (huQ : let P' := AsymptoticReconstructedCount.parameters A P
      u∈quotientSpace N P'.epsilon_pos (by omega : 1≤P'.s+4) x)
    (hv : let P' := AsymptoticReconstructedCount.parameters A P
      ∀ g,v g=(normalizer N P'.ε (P'.s+4) (g • x):ℂ)*u g) :
    let P' := AsymptoticReconstructedCount.parameters A P
    v∈AsymptoticQuotientIncidence.space N hN P'.epsilon_pos (by omega : 1≤P'.s+4) e x := by
  let P' := AsymptoticReconstructedCount.parameters A P
  apply (AsymptoticQuotientIncidence.space_mem N hN P'.epsilon_pos (by omega) e x v).mpr
  refine ⟨?_,?_,?_⟩
  · apply pointwise_weight_preserves_quotient N P'.epsilon_pos (by omega)
      (fun z => (normalizer N P'.ε (P'.s+4) z:ℂ)) _ x u v huQ hv
    intro h z
    rw [normalizer_invariant]
  · intro g
    simp only [coordinate_normalizer N P'.epsilon_pos (by omega) x u v hv]
    exact universalKernel_fricke A hN P K e x u hu g
  · intro p g
    simp only [coordinate_normalizer N P'.epsilon_pos (by omega) x u v hv]
    exact universalKernel_ramified A hN P K e x u hu p.val p.property.1 p.property.2 g

#print axioms universalKernel_normalized_transport

end AsymptoticRegularObservation
