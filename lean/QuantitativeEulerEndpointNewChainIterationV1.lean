module

public import QuantitativeEulerEndpointPrimeChainV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticIntegralSubgroup AsymptoticSubgroupSupport AsymptoticObservationStack
open QuantitativeSpectralObservability
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal

/-- Iteration of a proved fresh-prime loss with one numerical target.
The fixed containing space is retained through every actual source cut. -/
theorem primeChain_trace_bound_of_step (N : ℕ) (hN : 0<N) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (c : ℝ) (hc : 0<c) (target : ℝ)
    (V : ℍ → Submodule ℂ Space)
    (U : ℍ → ClosedSubmodule ℂ Space)
    (hmU : ∀ g h, Measurable (fun x => matrix (U x).toSubmodule.starProjection g h))
    (hcU : Covariant (fun x => (U x).toSubmodule.starProjection))
    (hf : trace volume (fun x => (U x).toSubmodule.starProjection)<∞)
    (hUV : ∀ x, (U x).toSubmodule≤V x)
    (l : List (EligiblePrime N)) (hnodup : l.Nodup)
    (hU : ∀ p∈l, ∀ x, Supported (integralGroup p.val) (U x).toSubmodule.starProjection)
    (hstep : ∀ p∈l, ∀ (F : ℍ → ClosedSubmodule ℂ Space),
      (∀ g h, Measurable (fun x => matrix (F x).toSubmodule.starProjection g h)) →
      Covariant (fun x => (F x).toSubmodule.starProjection) →
      (trace volume (fun x => (F x).toSubmodule.starProjection)<∞) →
      (∀ x, (F x).toSubmodule≤V x) →
      (∀ x, Supported (integralGroup p.val) (F x).toSubmodule.starProjection) →
      (p.val:ℝ)⁻¹*(cornerMass F-target)≤
        cornerMass F-cornerMass (closedPrimeStep N hN w hs hε t c F p)) :
    cornerMass (primeChain N hN w hs hε t c U l)-
        target≤
      (l.map primeFactor).prod*(cornerMass U-
        target) := by
  induction l generalizing U with
  | nil => simp only [primeChain,List.map_nil,List.prod_nil,one_mul,le_refl]
  | cons p l ih =>
    obtain ⟨hpnot,hln⟩ := List.nodup_cons.mp hnodup
    let U' := closedPrimeStep N hN w hs hε t c U p
    have hreg := fresh_step_source_regular N p.val hN p.property.2 w hs hε t
      (fun x => (U x).toSubmodule) hmU hcU (primeCut c p.val) (primeCut_pos c hc p.val)
    have hfin : trace volume (fun x => (U' x).toSubmodule.starProjection)<∞ :=
      fresh_step_source_trace_finite N p.val hN p.property.2 w hs hε t _ hf _
    have hsub (x : ℍ) : (U' x).toSubmodule≤(U x).toSubmodule :=
      fresh_step_source_le N p.val hN p.property.2 w hs hε t _ _ x
    have hsupp (r : EligiblePrime N) (hr : r∈l) (x : ℍ) :
        Supported (integralGroup r.val) (U' x).toSubmodule.starProjection := by
      apply fresh_step_source_supported N p.val hN p.property.2 w hs hε t _ r.val r.property.2
        (eligible_not_dvd_of_ne p r (fun he => hpnot (he ▸ hr)))
        (hU r (List.mem_cons_of_mem _ hr)) (primeCut c p.val) (primeCut_pos c hc p.val) x
    have htail := ih U' hreg.1 hreg.2 hfin (fun x => (hsub x).trans (hUV x)) hln hsupp
      (fun r hr => hstep r (List.mem_cons_of_mem _ hr))
    have hstep0 := hstep p List.mem_cons_self U hmU hcU hf hUV (hU p List.mem_cons_self)
    have hstep' : cornerMass U'-target≤
        primeFactor p*(cornerMass U-target) := by
      dsimp only [cornerMass,U',closedPrimeStep,primeFactor] at *
      linarith only [hstep0]
    calc
      _ ≤ (l.map primeFactor).prod*(cornerMass U'-
          target) := htail
      _ ≤ (l.map primeFactor).prod*(primeFactor p*(cornerMass U-
          target)) :=
        mul_le_mul_of_nonneg_left hstep' (primeProduct_nonneg l)
      _ = _ := by simp only [List.map_cons,List.prod_cons]; ring

#print axioms primeChain_trace_bound_of_step
end QuantitativeEulerEndpointPrepared
