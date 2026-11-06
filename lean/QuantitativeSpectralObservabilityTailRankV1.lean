module

public import QuantitativeSpectralObservabilityFundamentalTailV1
public import AsymptoticRegularSupportProjectionsV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticRegularTrace AsymptoticPolarIsometry
open scoped lp ENNReal

def fundamentalSubsetSpace (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (s : Set ℍ) (x : ℍ) : Submodule ℂ ℓ²(OrbitGroup,ℂ) :=
  (fundamentalSubsetProjection N hε ht s x).range

theorem fundamentalSubsetSpace_complete (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) {s : Set ℍ} (hs : s⊆fundamentalSet N) (x : ℍ) :
    CompleteSpace (fundamentalSubsetSpace N hε ht s x) :=
  (fundamentalSubsetProjection_star N hε ht hs x).isIdempotentElem.isClosed_range.completeSpace_coe

theorem fundamentalSubsetSpace_projection (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) {s : Set ℍ} (hs : s⊆fundamentalSet N) (x : ℍ) :
    letI := fundamentalSubsetSpace_complete N hε ht hs x
    (fundamentalSubsetSpace N hε ht s x).starProjection=
      fundamentalSubsetProjection N hε ht s x := by
  let : CompleteSpace (fundamentalSubsetSpace N hε ht s x) :=
    fundamentalSubsetSpace_complete N hε ht hs x
  obtain ⟨_,he⟩ := isStarProjection_iff_eq_starProjection_range.mp
    (fundamentalSubsetProjection_star N hε ht hs x)
  exact he.symm

/-- Every error with the actual tail projection as its left factor has
output rank bounded by the geometric tail area, independent of its norm. -/
theorem fundamentalTail_error_rank (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) {H : ℝ} (hH : 0<H)
    (B : ℍ → ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ)) :
    trace volume (fun x => (outputSpace
      ((fundamentalSubsetProjection N hε ht (fundamentalTail N H) x).comp (B x))).starProjection)≤
      (CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal H⁻¹) := by
  let s := fundamentalTail N H
  have hs : s⊆fundamentalSet N := inter_subset_left
  let (x : ℍ) : CompleteSpace (fundamentalSubsetSpace N hε ht s x) :=
    fundamentalSubsetSpace_complete N hε ht hs x
  have hsub (x : ℍ) : outputSpace
      ((fundamentalSubsetProjection N hε ht s x).comp (B x))≤
      fundamentalSubsetSpace N hε ht s x := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨v,rfl⟩
      exact ⟨B x v,rfl⟩
    · exact (fundamentalSubsetProjection_star N hε ht hs x).isIdempotentElem.isClosed_range
  have hm := projection_trace_mono volume _ _ hsub
  simp only [fundamentalSubsetSpace_projection N hε ht hs] at hm
  exact hm.trans (fundamentalTailProjection_trace N hN hε ht hH)

#print axioms fundamentalSubsetSpace_projection
#print axioms fundamentalTail_error_rank

end QuantitativeSpectralObservability
