module

public import QuantitativeEulerEndpointChainTraceV1
public import QuantitativeEulerEndpointCommonSourceV1
public import QuantitativeEulerEndpointBaselineExclusionsV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open QuantitativeArithmetic QuantitativeHolomorphic QuantitativeEulerDensityGenerators
open QuantitativeSpectralObservability AsymptoticObservationStack
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal

def closedBaselineSurvivor (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) (x : ℍ) :
    ClosedSubmodule ℂ Space where
  toSubmodule := goodBaselineSurvivor N H w hs hε t a x
  isClosed' := (completeSpace_coe_iff_isComplete.mp
    (inferInstance : CompleteSpace (goodBaselineSurvivor N H w hs hε t a x))).isClosed

/-- Actual trace-product bound for every finite list of distinct good
primes on one common region and one baseline source. No norm observability
or spectral loss is assumed: both follow from the prepared certificates. -/
theorem endpoint_chain_trace_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (hex : baselineDenominators N⊆excluded) {ε : ℝ} (hε : 0<ε) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ ∃ M : ℝ, 0≤M ∧
      ∀ C : ℝ, B≤C → ∀ X H : ℝ, max ε⁻¹ 4≤H → ∀ w : ℂ, w*w=1 →
      ∀ (t : ℕ) (ht : 1≤t),
      let L := (2*generatorTransportConstant P*C)*X^4
      let R := K*((integerCompactDistortion L H)^t)^2
      let hs := freshObservationRegion_compact L H hε
      let U := closedBaselineSurvivor N H w hs hε t (2*(1+R))⁻¹
      let c := Real.sqrt (2*(1+2*(M+R)))⁻¹
      ∀ l : List (EligiblePrime N), l.Nodup → (∀ p∈l, P.Good p.val ∧ (p.val : ℝ)≤X) →
      cornerMass (primeChain N (NeZero.pos N) w hs hε t c U l)-
          (trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal≤
        (l.map primeFactor).prod*(cornerMass U-
          (trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal) := by
  obtain ⟨B,hB,K,hK,M,hM,hbound⟩ := common_baseline_source_observability P hε
  refine ⟨B,hB,K,hK,M,hM,?_⟩
  intro C hBC X H hH w hw t ht L R hs U c l hnodup hl
  have hR : 0≤R := mul_nonneg hK (sq_nonneg _)
  have hJ : 0≤2*(M+R) := by positivity
  have ha := baseline_threshold_pos R hR
  have hcut := baseline_threshold_pos (2*(M+R)) hJ
  have hc : 0<c := Real.sqrt_pos.mpr hcut
  have hsmall : (2*(M+R))*c^2<1 := by
    rw [show c^2=(2*(1+2*(M+R)))⁻¹ from Real.sq_sqrt hcut.le]
    exact (baseline_threshold_small _ hJ).trans_lt (by norm_num)
  have hreg := good_baseline_survivor_regular N H w hs hε t (2*(1+R))⁻¹ ha
  apply primeChain_trace_bound N (NeZero.pos N) w hs hε t c hc H
    (le_trans (by norm_num : (0 : ℝ)≤4) ((le_max_right _ _).trans hH)) ht
    (2*(M+R)) hJ hsmall U hreg.1 hreg.2
    (good_baseline_survivor_trace_finite N H w hs hε t (2*(1+R))⁻¹) l hnodup
  · intro p hp x
    exact good_baseline_survivor_supported N p.val p.property.2
      (good_prime_avoids_baseline P hex p.val (hl p hp).1) H w hs hε t (2*(1+R))⁻¹ ha x
  · intro p hp x v hv
    by_cases hx : fundamentalGood N x
    · have hv' : v∈baselineSurvivor N H w hs hε t x (2*(1+R))⁻¹ := by
        simpa only [U,closedBaselineSurvivor,goodBaselineSurvivor,
          QuantitativeSpectralExceptionalGoodRoot.source,ite_eq_left hx] using hv
      obtain ⟨hqN,hqbound⟩ := hbound C hBC X p.val (hl p hp).1 (hl p hp).2
      have he := hqbound H hH w hw t ht x hx v hv'
      have hMf := mul_nonneg hM (sq_nonneg ‖stack
        (fun i => AsymptoticFreshCompactDefects.row N p.val (NeZero.pos N) p.property.2 w hs hε t i x) v‖)
      have hRs := mul_nonneg hR (sq_nonneg ‖fundamentalSampling N (NeZero.pos N) H hε ht x v‖)
      nlinarith only [he,hMf,hRs]
    · have hv0 : v=0 := by
        simpa only [U,closedBaselineSurvivor,goodBaselineSurvivor,
          QuantitativeSpectralExceptionalGoodRoot.source,ite_eq_right hx,Submodule.mem_bot] using hv
      simp only [hv0,map_zero,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),zero_add,mul_zero,le_refl]

#print axioms endpoint_chain_trace_bound
end QuantitativeEulerEndpointPrepared
