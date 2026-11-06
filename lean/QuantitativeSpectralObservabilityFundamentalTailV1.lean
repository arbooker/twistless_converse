module

public import QuantitativeSpectralObservabilityFundamentalTransportV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticRegularTrace AsymptoticOrbitDiagonal
open scoped lp ENNReal

/-- The quotient projection corresponding to a geometric subset of the
actual fundamental domain. It vanishes on the invariant null boundary. -/
def fundamentalSubsetProjection (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (s : Set ℍ) (x : ℍ) : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  (fundamentalTransport N hε ht s x).comp (fundamentalTransport N hε ht s x).adjoint

theorem fundamentalSubsetProjection_star (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) {s : Set ℍ} (hs : s⊆fundamentalSet N) (x : ℍ) :
    IsStarProjection (fundamentalSubsetProjection N hε ht s x) := by
  constructor
  · change (fundamentalSubsetProjection N hε ht s x).comp
      (fundamentalSubsetProjection N hε ht s x)=_
    by_cases hx : fundamentalGood N x
    · have hr : (fundamentalTransport N hε ht s x).comp (corner s x)=
          fundamentalTransport N hε ht s x := by
        simp only [fundamentalTransport,comp_assoc,corner_idempotent]
      unfold fundamentalSubsetProjection
      calc
        _ = ((fundamentalTransport N hε ht s x).comp
          ((fundamentalTransport N hε ht s x).adjoint.comp
            (fundamentalTransport N hε ht s x))).comp
          (fundamentalTransport N hε ht s x).adjoint := by simp only [comp_assoc]
        _ = _ := by simp only [fundamentalTransport_gram N hε ht hs x hx,hr]
    · simp only [fundamentalSubsetProjection,fundamentalTransport_zero N hε ht s x hx,
        zero_comp]
  · change (fundamentalSubsetProjection N hε ht s x).adjoint=_
    simp only [fundamentalSubsetProjection,adjoint_comp,adjoint_adjoint]

theorem fundamentalSubsetProjection_range (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (s : Set ℍ) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ)) :
    fundamentalSubsetProjection N hε ht s x v∈quotientSpace N hε ht x :=
  fundamentalTransfer_range N hε ht x _

theorem fundamentalSubsetProjection_regular (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) {s : Set ℍ} (hs : MeasurableSet s) :
    (∀ g h, Measurable (fun x => matrix (fundamentalSubsetProjection N hε ht s x) g h)) ∧
      Covariant (fundamentalSubsetProjection N hε ht s) := by
  have hr := fundamentalTransport_regular N hN hε ht hs
  exact ⟨matrix_comp_measurable _ _ hr.1 (matrix_adjoint_measurable _ hr.1),
    covariant_comp _ _ hr.2 (covariant_adjoint _ hr.2)⟩

/-- Exact trace preservation under the actual partial isometry. In
particular, geometric exceptional area is also quotient exceptional rank. -/
theorem fundamentalSubsetProjection_trace (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) {s : Set ℍ} (hm : MeasurableSet s)
    (hs : s⊆fundamentalSet N) :
    trace volume (fundamentalSubsetProjection N hε ht s)=volume s := by
  have hr := fundamentalTransport_regular N hN hε ht hm
  change trace volume (fun x => (fundamentalTransport N hε ht s x).comp
    (fundamentalTransport N hε ht s x).adjoint)=volume s
  rw [← rational_trace_adjoint_mul (fundamentalTransport N hε ht s) hr.1 hr.2]
  calc
    _ = trace volume (corner (G:=OrbitGroup) s) := by
      unfold trace
      apply lintegral_congr_ae
      filter_upwards [fundamentalGood_ae N hN] with x hx
      exact congrArg (fun B : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) =>
        ENNReal.ofReal (matrix B 1 1).re) (fundamentalTransport_gram N hε ht hs x hx)
    _ = volume s := trace_corner volume hm

def fundamentalTail (N : ℕ) (H : ℝ) : Set ℍ :=
  fundamentalSet N ∩ wideTailCover N H

theorem fundamentalTail_measurable (N : ℕ) (hN : 0<N) (H : ℝ) :
    MeasurableSet (fundamentalTail N H) :=
  (fundamentalSet_measurable N hN).inter (wideTailCover_measurable N hN H)

theorem fundamentalTailProjection_trace (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) {H : ℝ} (hH : 0<H) :
    trace volume (fundamentalSubsetProjection N hε ht (fundamentalTail N H)) ≤
      (CongruenceSubgroup.Gamma0 N).index * (3*ENNReal.ofReal H⁻¹) := by
  rw [fundamentalSubsetProjection_trace N hN hε ht (fundamentalTail_measurable N hN H)
    (inter_subset_left)]
  exact (measure_mono (inter_subset_right : fundamentalTail N H⊆wideTailCover N H)).trans
    (wideTailCover_area N hN hH)

#print axioms fundamentalSubsetProjection_star
#print axioms fundamentalSubsetProjection_regular
#print axioms fundamentalSubsetProjection_trace
#print axioms fundamentalTailProjection_trace

end QuantitativeSpectralObservability
