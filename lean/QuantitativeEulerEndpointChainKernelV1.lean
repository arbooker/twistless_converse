module

public import QuantitativeEulerEndpointChainSourceV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane ContinuousLinearMap AsymptoticRegularTrace
open QuantitativeSpectralCornerCutRow AsymptoticPolarIsometry
open AsymptoticRegularObservationRows AsymptoticHyperbolicArea
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

theorem baseline_kernel_survives (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (a : ℝ)
    (v : Space) (hv : v∈AsymptoticOrbitRegion.Space (terminal ε\terminal H) x)
    (hz : baselineStack N w hs hε t x v=0) :
    v∈baselineSurvivor N H w hs hε t x a := by
  apply QuantitativeSpectralCornerCutRow.kernel_survives _ _ _ hv
  apply norm_eq_zero.mp
  rw [←absolute_norm,hz,norm_zero]

theorem closed_baseline_kernel_survives (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (a : ℝ)
    (hx : QuantitativeSpectralObservability.fundamentalGood N x)
    (v : Space) (hv : v∈AsymptoticOrbitRegion.Space (terminal ε\terminal H) x)
    (hz : baselineStack N w hs hε t x v=0) :
    v∈(closedBaselineSurvivor N H w hs hε t a x).toSubmodule := by
  simpa only [closedBaselineSurvivor,goodBaselineSurvivor,
    QuantitativeSpectralExceptionalGoodRoot.source,ite_eq_left hx] using
    baseline_kernel_survives N H w hs hε t x a v hv hz

/-- Exact common solutions of the original twist equations survive every
constructed cut, with no lower bound on the positive spectral thresholds. -/
theorem primeChain_kernel_survives (N : ℕ) (hN : 0<N) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (c : ℝ)
    (U : ℍ → ClosedSubmodule ℂ Space) (l : List (EligiblePrime N)) (x : ℍ)
    (v : Space) (hv : v∈(U x).toSubmodule)
    (hz : ∀ p∈l, twist N p.val hN p.property.1.pos w hs hε t x v=0) :
    v∈(primeChain N hN w hs hε t c U l x).toSubmodule := by
  induction l generalizing U with
  | nil => exact hv
  | cons p l ih =>
    apply ih (closedPrimeStep N hN w hs hε t c U p) _
      (fun r hr => hz r (List.mem_cons_of_mem _ hr))
    change v∈freshStepSource N p.val hN p.property.2 w hs hε t
      (fun y => (U y).toSubmodule) (primeCut c p.val) x
    rw [fresh_step_source_eq_original]
    apply QuantitativeSpectralCornerCutRow.kernel_survives _ _ _ hv
    simp only [normalizedSourceTwist,_root_.smul_apply,comp_apply,
      (U x).toSubmodule.starProjection_eq_self_iff.mpr hv,hz p List.mem_cons_self,smul_zero]

#print axioms baseline_kernel_survives
#print axioms closed_baseline_kernel_survives
#print axioms primeChain_kernel_survives
end QuantitativeEulerEndpointPrepared
