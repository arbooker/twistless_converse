module

public import QuantitativeEulerEndpointPacketGramV1
public import QuantitativeEulerEndpointPacketRegularV1
public import QuantitativeEulerEndpointChainDecayV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace
open QuantitativeEulerDensityGenerators QuantitativeHolomorphic QuantitativeSpectralDeflationChain
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

def packetChain (N : ℕ) (hN : 0<N) (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (c : ℝ) (U : ℍ → ClosedSubmodule ℂ Space)
    (l : List (EligiblePrime N)) (x : ℍ) : ClosedSubmodule ℂ Space :=
  chain (U x) (fun i => packetSequence N hN w hs hε t l i x) c l.length

theorem packetChain_mass_eq (N : ℕ) (hN : 0<N) (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (c : ℝ) (hc : 0<c) (U : ℍ → ClosedSubmodule ℂ Space)
    (l : List (EligiblePrime N)) :
    cornerMass (packetChain N hN w hs hε t c U l)=cornerMass (primeChain N hN w hs hε t c U l) := by
  have he : packetChain N hN w hs hε t c U l=primeChain N hN w hs hε t c U l :=
    funext (fun x => (primeChain_eq_packet N hN w hs hε t c hc U l x).symm)
  rw [he]

/-- The checked logarithmic survivor trace belongs to the existing
fixed-threshold packet built from explicit raw original-twist rows. -/
theorem prepared_packet_trace_decay (N : ℕ) [NeZero N] (hN : 2≤N)
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
      cornerMass (packetChain N (NeZero.pos N) w hs hε t c U (goodPrimeList P n))≤
        (trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal+
          ε⁻¹*A/Real.log (n+1 : ℝ) := by
  intro P
  obtain ⟨B,hB,K,hK,M,hM,A,hA,hbound⟩ := prepared_chain_trace_decay N hN excluded hex threshold hε
  refine ⟨B,hB,K,hK,M,hM,A,hA,?_⟩
  intro C hBC n hn H hH w hw t ht L R hs U c
  have hR : 0≤R := mul_nonneg hK (sq_nonneg _)
  have hJ : 0≤2*(M+R) := by positivity
  have hc : 0<c := Real.sqrt_pos.mpr (baseline_threshold_pos (2*(M+R)) hJ)
  rw [packetChain_mass_eq N (NeZero.pos N) w hs hε t c hc U (goodPrimeList P n)]
  exact hbound C hBC n hn H hH w hw t ht

#print axioms packetChain_mass_eq
#print axioms prepared_packet_trace_decay
end QuantitativeEulerEndpointPrepared
