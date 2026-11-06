module

public import QuantitativeEulerEndpointPrimeStepV1
public import QuantitativeEulerEndpointCompressedSourceV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open QuantitativeArithmetic QuantitativeHolomorphic QuantitativeEulerDensityGenerators
open QuantitativeSpectralObservability AsymptoticObservationStack
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal

/-- One actual fresh-prime trace loss, with theta=1/q, from the original
fixed rows and the proved endpoint norm estimate. All regularity, subgroup
support, finite traces and observability are proved for the displayed source.
The comparison target here is the full normalized congruence quotient. -/
theorem endpoint_fresh_trace_loss {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    {ε : ℝ} (hε : 0<ε) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ ∃ M : ℝ, 0≤M ∧
      ∀ C : ℝ, B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, (∀ a : UnitResidue N, ¬q∣(primeLift N a).q) →
      ∀ H : ℝ, max ε⁻¹ 4≤H → ∀ w : ℂ, w*w=1 → ∀ (t : ℕ) (ht : 1≤t),
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      let R := K*((integerCompactDistortion L H)^t)^2
      let hs := freshObservationRegion_compact L H hε
      let U := goodBaselineSurvivor N H w hs hε t (2*(1+R))⁻¹
      let J := 2*(M+R)
      let d := Real.sqrt ((2*(1+J))⁻¹*(q : ℝ)⁻¹/(2*((q-1 : ℕ) : ℝ)))
      (q : ℝ)⁻¹*((trace volume (fun x => (U x).starProjection)).toReal-
        (trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal)≤
      (trace volume (fun x => (U x).starProjection)).toReal-
        (trace volume (fun x => (freshStepSource N q (NeZero.pos N) hqN w hs hε t U d x).starProjection)).toReal := by
  obtain ⟨B,hB,K,hK,M,hM,hbound⟩ := compressed_baseline_source_observability P hε
  refine ⟨B,hB,K,hK,M,hM,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := hbound C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro hqfixed H hH w hw t ht
  dsimp only
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  let R := K*((integerCompactDistortion L H)^t)^2
  let hs := freshObservationRegion_compact L H hε
  let U := goodBaselineSurvivor N H w hs hε t (2*(1+R))⁻¹
  let J := 2*(M+R)
  let c := Real.sqrt (2*(1+J))⁻¹
  let d := Real.sqrt ((2*(1+J))⁻¹*(q : ℝ)⁻¹/(2*((q-1 : ℕ) : ℝ)))
  have hR : 0≤R := mul_nonneg hK (sq_nonneg _)
  have hJ : 0≤J := by dsimp [J]; positivity
  have ha := baseline_threshold_pos R hR
  have hcut := baseline_threshold_pos J hJ
  have hc : 0<c := Real.sqrt_pos.mpr hcut
  have hc2 : c^2=(2*(1+J))⁻¹ := Real.sq_sqrt hcut.le
  have hq : 0<(q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  have hqm : 0<((q-1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt
  have hdarg : 0<(2*(1+J))⁻¹*(q : ℝ)⁻¹/(2*((q-1 : ℕ) : ℝ)) := by positivity
  have hd : 0<d := Real.sqrt_pos.mpr hdarg
  have hscale : d^2=c^2*(q : ℝ)⁻¹/(2*((q-1 : ℕ) : ℝ)) := by
    rw [hc2]
    exact Real.sq_sqrt hdarg.le
  have hsmall : J*c^2<1 := by
    rw [hc2]
    exact (baseline_threshold_small J hJ).trans_lt (by norm_num)
  have hreg := good_baseline_survivor_regular N H w hs hε t (2*(1+R))⁻¹ ha
  have hobs (x : ℍ) (v : Space) (hv : v∈U x) :
      ‖v‖^2≤J*(‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w hs hε t i x) v‖^2+
        ‖fundamentalSampling N (NeZero.pos N) H hε ht x v‖^2) := by
    by_cases hx : fundamentalGood N x
    · have hv' : v∈baselineSurvivor N H w hs hε t x (2*(1+R))⁻¹ := by
        simpa only [U,goodBaselineSurvivor,QuantitativeSpectralExceptionalGoodRoot.source,ite_eq_left hx] using hv
      have he := hqbound H hH w hw t ht x hx v hv'
      have hMf := mul_nonneg hM (sq_nonneg ‖stack
        (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w hs hε t i x) v‖)
      have hRs := mul_nonneg hR (sq_nonneg ‖fundamentalSampling N (NeZero.pos N) H hε ht x v‖)
      change ‖v‖^2≤2*(M+R)*_ 
      nlinarith only [he,hMf,hRs]
    · have hv0 : v=0 := by
        simpa only [U,goodBaselineSurvivor,QuantitativeSpectralExceptionalGoodRoot.source,
          ite_eq_right hx,Submodule.mem_bot] using hv
      simp only [hv0,map_zero,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),zero_add,mul_zero,le_refl]
  exact source_prime_trace_loss N q (NeZero.pos N) hqN w hs hε t U hreg.1 hreg.2
    (good_baseline_survivor_supported N q hqN hqfixed H w hs hε t (2*(1+R))⁻¹ ha)
    (good_baseline_survivor_trace_finite N H w hs hε t (2*(1+R))⁻¹)
    H (le_trans (by norm_num : (0 : ℝ)≤4) ((le_max_right _ _).trans hH)) ht
    hc hd hJ hsmall hscale hobs

#print axioms endpoint_fresh_trace_loss
end QuantitativeEulerEndpointPrepared
