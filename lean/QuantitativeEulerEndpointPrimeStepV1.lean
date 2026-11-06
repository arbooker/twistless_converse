module

public import QuantitativeEulerEndpointCompressedRowsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup AsymptoticObservationStack
open QuantitativeSpectralObservability QuantitativeSpectralFreshStep
open QuantitativeSpectralCornerCutRow AsymptoticMixing
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hqN : ¬q∣N)
variable (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
variable (U : ℍ → Submodule ℂ Space) [∀ x, CompleteSpace (U x)]

/-- Actual one-prime update of a source using the normalized original mixed row. -/
def freshStepSource (d : ℝ) (x : ℍ) : Submodule ℂ Space :=
  nextSpace (U x) (normalizedMixed (primeLabels q) (freshSourceRows N q hN hqN w hs hε t U x)) d

instance fresh_step_source_complete (d : ℝ) (x : ℍ) :
    CompleteSpace (freshStepSource N q hN hqN w hs hε t U d x) := by
  unfold freshStepSource
  infer_instance

/-- Concrete rows and normalized quotient sampling discharge the regularity,
boundedness and mapping requirements of the fresh trace theorem. The norm
observability hypothesis is supplied by the endpoint source theorem below. -/
theorem source_prime_trace_loss
    (hmU : ∀ g h, Measurable (fun x => matrix (U x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection))
    (hU : ∀ x, Supported (integralGroup q) (U x).starProjection)
    (hf : trace volume (fun x => (U x).starProjection)<∞)
    (H : ℝ) (hH : 0≤H) (ht : 1≤t)
    {c d K : ℝ} (hc : 0<c) (hd : 0<d) (hK : 0≤K) (hsmall : K*c^2<1)
    (hscale : d^2=c^2*(q : ℝ)⁻¹/(2*((q-1 : ℕ) : ℝ)))
    (hobs : ∀ x v, v∈U x → ‖v‖^2≤K*(
      ‖stack (fun i => AsymptoticFreshCompactDefects.row N q hN hqN w hs hε t i x) v‖^2+
      ‖fundamentalSampling N hN H hε ht x v‖^2)) :
    (q : ℝ)⁻¹*((trace volume (fun x => (U x).starProjection)).toReal-
      (trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal)≤
    (trace volume (fun x => (U x).starProjection)).toReal-
      (trace volume (fun x => (freshStepSource N q hN hqN w hs hε t U d x).starProjection)).toReal := by
  obtain ⟨M,hM⟩ := fresh_source_stack_bounded N q hN hqN w hs hε t U
  obtain ⟨MC,hMC⟩ := source_sampling_bounded N hN hε t U H hH ht
  have hL := fresh_source_rows_regular N q hN hqN w hs hε t U hmU hcU
  have hC := source_sampling_regular N hN hε t U H ht hmU hcU
  have hq : 1<(q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have hcard : 0<Fintype.card (Fin (q-1)) := by
    simpa only [Fintype.card_fin] using Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt
  have hobs' (x : ℍ) (v : Space) (hv : v∈U x) :
      ‖v‖^2≤K*(‖stack (freshSourceRows N q hN hqN w hs hε t U x) v‖^2+
        ‖sourceSampling N hN hε t U H ht x v‖^2) := by
    have he : stack (freshSourceRows N q hN hqN w hs hε t U x) v=
        stack (fun i => AsymptoticFreshCompactDefects.row N q hN hqN w hs hε t i x) v := by
      ext i : 1
      exact fresh_source_rows_apply N q hN hqN w hs hε t U x i v hv
    rw [he]
    simpa only [sourceSampling,comp_apply,(U x).starProjection_eq_self_iff.mpr hv] using hobs x v hv
  have htheta : (q : ℝ)⁻¹≤1 := (inv_le_one₀ (by linarith)).mpr (le_of_lt hq)
  have hh := observable_fresh_step volume AsymptoticRationalGroup.measurePreserving
    (integralGroup q) (primeLabels q) (primeLabels_separated q) hcard U
    (AsymptoticCongruenceQuotient.quotientSpace N hε ht) hmU hcU
    (freshSourceRows N q hN hqN w hs hε t U) (fun i => (hL i).1) (fun i => (hL i).2)
    (fresh_source_rows_supported N q hN hqN w hs hε t U hU)
    (fresh_source_rows_fixed N q hN hqN w hs hε t U)
    (sourceSampling N hN hε t U H ht) hC.1 hC.2 M MC hM hMC hf
    (AsymptoticCongruenceQuotient.projection_trace_finite N hN hε ht)
    hc hd (inv_pos.mpr (by linarith)) htheta
    (by simpa only [Fintype.card_fin] using hscale) hK hsmall hobs'
    (fun x v _ => source_sampling_range N hN hε t U H ht x v)
  have hfactor : (1-(q : ℝ)⁻¹)/(Fintype.card (Fin (q-1)) : ℝ)=(q : ℝ)⁻¹ := by
    rw [Fintype.card_fin,Nat.cast_sub (Fact.out : q.Prime).one_lt.le,Nat.cast_one]
    field_simp [ne_of_gt (lt_trans zero_lt_one hq),ne_of_gt (sub_pos.mpr hq)]
  rw [hfactor] at hh
  exact hh

#print axioms source_prime_trace_loss
end QuantitativeEulerEndpointPrepared
