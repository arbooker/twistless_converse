module

public import QuantitativeEulerEndpointChainSourceV1
public import QuantitativeEulerEndpointPrimeListV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticHyperbolicArea
open QuantitativeEulerDensityGenerators QuantitativeHolomorphic
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal

theorem closedBaseline_mass_le (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) :
    cornerMass (closedBaselineSurvivor N H w hs hε t a)≤ε⁻¹ := by
  have hb : trace volume (fun x => (goodBaselineSurvivor N H w hs hε t a x).starProjection)≤
      ENNReal.ofReal ε⁻¹ := by
    rw [good_baseline_survivor_trace]
    apply (baseline_survivor_trace_le N H w hs hε t a).trans
    rw [←terminal_area hε]
    exact measure_mono Set.sdiff_subset
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  change (trace volume (fun x => (goodBaselineSurvivor N H w hs hε t a x).starProjection)).toReal≤ε⁻¹
  simpa only [ENNReal.toReal_ofReal (inv_nonneg.mpr hε.le)] using ht

/-- Unconditional logarithmic trace decay of the actual constructed
successive-cut survivor for the summable-exception preparation. The target
is the full normalized congruence quotient; no small-spectrum or finite
Euler-count transfer is asserted here. -/
theorem prepared_chain_trace_decay (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (hex : baselineDenominators N⊆excluded) (threshold : ℕ)
    {ε : ℝ} (hε : 0<ε) :
    let P := prepared N hN excluded threshold
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ ∃ M : ℝ, 0≤M ∧ ∃ A : ℝ, 0<A ∧
      ∀ C : ℝ, B≤C → ∀ n : ℕ, 0<n → ∀ H : ℝ, max ε⁻¹ 4≤H →
      ∀ w : ℂ, w*w=1 → ∀ (t : ℕ) (ht : 1≤t),
      let L := (2*generatorTransportConstant P*C)*(n : ℝ)^4
      let R := K*((integerCompactDistortion L H)^t)^2
      let hs := freshObservationRegion_compact L H hε
      let U := closedBaselineSurvivor N H w hs hε t (2*(1+R))⁻¹
      let c := Real.sqrt (2*(1+2*(M+R)))⁻¹
      cornerMass (primeChain N (NeZero.pos N) w hs hε t c U (goodPrimeList P n))≤
        (trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal+
          ε⁻¹*A/Real.log (n+1 : ℝ) := by
  intro P
  obtain ⟨B,hB,K,hK,M,hM,hbound⟩ := endpoint_chain_trace_bound P hex hε
  obtain ⟨A,hA,hprod⟩ := goodPrimeList_prepared_product N hN excluded threshold
  refine ⟨B,hB,K,hK,M,hM,A,hA,?_⟩
  intro C hBC n hn H hH w hw t ht L R hs U c
  have hl (p : EligiblePrime N) (hp : p∈goodPrimeList P n) : P.Good p.val ∧ (p.val : ℝ)≤(n : ℝ) := by
    obtain ⟨hg,hpn⟩ := goodPrimeList_mem P n p hp
    exact ⟨hg,by exact_mod_cast hpn⟩
  have hchain := hbound C hBC n H hH w hw t ht (goodPrimeList P n) (goodPrimeList_nodup P n) hl
  have hmass : cornerMass U≤ε⁻¹ := closedBaseline_mass_le N H w hs hε t _
  have hbase : cornerMass U-(trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal≤ε⁻¹ :=
    (sub_le_self _ ENNReal.toReal_nonneg).trans hmass
  have hb := (mul_le_mul_of_nonneg_left hbase (primeProduct_nonneg (goodPrimeList P n))).trans
    (mul_le_mul_of_nonneg_right (hprod n hn) (inv_nonneg.mpr hε.le))
  have he : (A/Real.log (n+1 : ℝ))*ε⁻¹=ε⁻¹*A/Real.log (n+1 : ℝ) := by ring
  rw [he] at hb
  exact (sub_le_iff_le_add.mp (hchain.trans hb)).trans_eq (add_comm _ _)

#print axioms closedBaseline_mass_le
#print axioms prepared_chain_trace_decay
end QuantitativeEulerEndpointPrepared
