module

public import AsymptoticIncidenceOrthogonalityV1
public import AsymptoticOrthogonalProjectionSumV1
public import AsymptoticIncidenceCountReductionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticQuotientIncidence

open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns
open scoped lp ENNReal

/-- All actual incidence sectors can be added inside one common corner.
Only its total trace occurs; individual sector dimensions and local
reversal traces are unnecessary. -/
theorem totalTrace_le_common (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (U : ℍ → Submodule ℂ ℓ²(AsymptoticRationalGroup.Group,ℂ)) [∀ x,CompleteSpace (U x)]
    (hU : ∀ e : Sector N,∀ x,space N hN hε ht e x≤U x)
    (hf : trace volume (fun x => (U x).starProjection)<∞) :
    totalTrace N hN hε ht≤(trace volume (fun x => (U x).starProjection)).toReal :=
  sum_projection_trace_toReal_le volume (fun e x => space N hN hε ht e x)
    (fun x e d hed => space_le_orthogonal N hN hε ht e d hed x) U hU hf

#print axioms totalTrace_le_common

end AsymptoticQuotientIncidence
