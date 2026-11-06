module

public import QuantitativeEulerEndpointBaselineCutV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic QuantitativeEulerDensityGenerators
open QuantitativeSpectralObservability QuantitativeSpectralExceptionalReducedRows
open AsymptoticRegularObservationRows AsymptoticObservationStack
open AsymptoticHyperbolicArea AsymptoticOrbitDiagonal
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

def baselineTerminalSource (N : ℕ) [NeZero N] (H : ℝ) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (a : ℝ) :
    Submodule ℂ Space :=
  AsymptoticOrbitRegion.Space (terminal ε\terminal H) x ⊓ baselineLowSpace N w hs hε t x a

private theorem absorb_baseline (n s a f R : ℝ) (h : n≤s+R*(a+f)) (ha : R*a≤n/2) :
    n≤2*s+2*R*f := by nlinarith only [h,ha]

/-- An explicit low spectral cut of the actual original fixed rows gives
source observability by the actual fresh-prime rows and normalized quotient
sampler. The energy threshold is 1/(2*(1+R)), R=K*D(L,H)^(2t).
No small-row inequality or observability conclusion is assumed. -/
theorem fundamental_low_source_observability {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    {ε : ℝ} (hε : 0<ε) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ ∃ M : ℝ, 0≤M ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (H : ℝ), max ε⁻¹ 4≤H → ∀ (w : ℂ), w*w=1 →
      ∀ (t : ℕ) (ht : 1≤t) (x : ℍ), fundamentalGood N x →
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      let R := K*((integerCompactDistortion L H)^t)^2
      ∀ v : Space, v∈baselineTerminalSource N H w (freshObservationRegion_compact L H hε)
        hε t x (2*(1+R))⁻¹ →
      ‖v‖^2≤2*M*‖fundamentalSampling N (NeZero.pos N) H hε ht x v‖^2+
        2*R*‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
          (freshObservationRegion_compact L H hε) hε t i x) v‖^2 := by
  obtain ⟨B,hB,K,hK,M,hM,hbound⟩ := fundamental_terminal_original_fresh_energy P hε
  refine ⟨B,hB,K,hK,M,hM,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := hbound C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro H hH w hw t ht x hx L R v hv
  have hR : 0≤R := mul_nonneg hK (sq_nonneg _)
  have hc := difference_source_corners (terminal ε) (terminal H) x v hv.1
  have he := hqbound H hH w hw t ht x hx v
  dsimp only at he
  rw [hc.1,hc.2,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),add_zero] at he
  have hl := baseline_low_energy N w (freshObservationRegion_compact L H hε) hε t x
    (2*(1+R))⁻¹ v hv.2
  have hb := (mul_le_mul_of_nonneg_left hl hR).trans
    ((mul_assoc _ _ _).symm.trans_le
      (mul_le_mul_of_nonneg_right (baseline_threshold_small R hR) (sq_nonneg ‖v‖)))
  have hb' : R*(‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w
      (freshObservationRegion_compact L H hε) hε t x v‖^2+
      ‖fixedPrimeStack N w (freshObservationRegion_compact L H hε) hε t x v‖^2)≤‖v‖^2/2 :=
    hb.trans_eq (by ring)
  exact (absorb_baseline _ _ _ _ R he hb').trans_eq (by ring)

#print axioms fundamental_low_source_observability
end QuantitativeEulerEndpointPrepared
