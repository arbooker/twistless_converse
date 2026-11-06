module

public import AsymptoticDecodedQuotientV1
public import AsymptoticReconstructionStripSupportV1
public import AsymptoticUniversalObservationKernelV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticCongruenceQuotient
open AsymptoticCompactObservationCount AsymptoticRegularReconstruction
open AsymptoticSectorSigns FinitenessCertificate FinitenessGlobalHeight
open AsymptoticRegularCompactBranch (Space)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Every vector in the concrete full observation kernel belongs to
the quotient Hilbert space under the constructed induction isometry.
No quotient equation or invariance hypothesis is added to the kernel. -/
theorem universalKernel_ae_quotient_range (hN : 0<N) (P : Parameters A)
    (K : CompactExhaustion ℍ) (e : Sector N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ∀ᵐ x ∂volume,globalKernelSpace A hN P (universalRows N) K e x≤
      (induction N P'.epsilon_pos (by omega : 1≤P'.s+4) x).toLinearMap.range := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hi := universalKernel_ae_congruence_invariant A hN P K e
  filter_upwards [hi] with x hx
  intro v hv
  apply range_of_decode N P'.epsilon_pos (by omega) x v
  · have hm := (universalKernel_mem A hN P K e x v).mp hv
    obtain ⟨f,hf⟩ := hm.1
    intro g hg
    rw [← hf]
    apply includedExtension_zero_off_strip A hN P' (multiplier e) x _ f g hg
    exact (parameters_contraction A hN P (multiplier e)
      (fun q _ => multiplier_norm e q) x).trans (by norm_num)
  · intro h g
    have hh := hx (representative h) (representative_mem h) v hv g
    rw [representative_label] at hh
    exact hh

#print axioms universalKernel_ae_quotient_range

end AsymptoticRegularObservation
