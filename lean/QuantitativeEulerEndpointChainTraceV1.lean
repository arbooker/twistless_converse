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

/-- The actual successive original-twist cuts obey the Euler product
trace bound. The only norm hypothesis concerns the initial source;
all later source bounds follow by inclusion. -/
theorem primeChain_trace_bound (N : ℕ) (hN : 0<N) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (c : ℝ) (hc : 0<c) (H : ℝ) (hH : 0≤H) (ht : 1≤t)
    (K : ℝ) (hK : 0≤K) (hsmall : K*c^2<1)
    (U : ℍ → ClosedSubmodule ℂ Space)
    (hmU : ∀ g h, Measurable (fun x => matrix (U x).toSubmodule.starProjection g h))
    (hcU : Covariant (fun x => (U x).toSubmodule.starProjection))
    (hf : trace volume (fun x => (U x).toSubmodule.starProjection)<∞)
    (l : List (EligiblePrime N)) (hnodup : l.Nodup)
    (hU : ∀ p∈l, ∀ x, Supported (integralGroup p.val) (U x).toSubmodule.starProjection)
    (hobs : ∀ p∈l, ∀ x v, v∈(U x).toSubmodule →
      ‖v‖^2≤K*(‖stack (fun i => AsymptoticFreshCompactDefects.row N p.val hN p.property.2 w hs hε t i x) v‖^2+
        ‖fundamentalSampling N hN H hε ht x v‖^2)) :
    cornerMass (primeChain N hN w hs hε t c U l)-
        (trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal≤
      (l.map primeFactor).prod*(cornerMass U-
        (trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal) := by
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
    have hob (r : EligiblePrime N) (hr : r∈l) (x : ℍ) (v : Space) (hv : v∈(U' x).toSubmodule) :=
      hobs r (List.mem_cons_of_mem _ hr) x v (hsub x hv)
    have htail := ih U' hreg.1 hreg.2 hfin hln hsupp hob
    have hstep := source_prime_trace_loss N p.val hN p.property.2 w hs hε t
      (fun x => (U x).toSubmodule) hmU hcU (hU p List.mem_cons_self) hf H hH ht
      hc (primeCut_pos c hc p.val) hK hsmall (primeCut_sq c p.val) (hobs p List.mem_cons_self)
    have hstep' : cornerMass U'-(trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal≤
        primeFactor p*(cornerMass U-(trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal) := by
      dsimp only [cornerMass,U',closedPrimeStep,primeFactor] at *
      linarith only [hstep]
    calc
      _ ≤ (l.map primeFactor).prod*(cornerMass U'-
          (trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal) := htail
      _ ≤ (l.map primeFactor).prod*(primeFactor p*(cornerMass U-
          (trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal)) :=
        mul_le_mul_of_nonneg_left hstep' (primeProduct_nonneg l)
      _ = _ := by simp only [List.map_cons,List.prod_cons]; ring

#print axioms primeChain_trace_bound
end QuantitativeEulerEndpointPrepared
