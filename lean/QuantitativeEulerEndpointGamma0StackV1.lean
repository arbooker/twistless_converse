module

public import QuantitativeEulerEndpointGamma0ControlV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open AsymptoticRegularObservationRows AsymptoticObservationStack
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- The actual full finite Gamma0 generator detector is bounded by the
original untwisted row, the original fixed-prime averaged-row stack, and
the actual shifted fresh-prime stack, on ONE shared observation region.
The finite generating set has closure exactly Gamma0(N). -/
theorem full_gamma0_generator_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (w : ℂ) (_hw : w*w=1)
        {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      ‖stack (fun γ : ↥(observedGenerators N) =>
        AsymptoticCongruenceDefect.operator γ.val hs hε t x) v‖^2≤
      K*((integerCompactDistortion L H)^t)^2*
        (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
          ‖fixedPrimeStack N w (freshObservationRegion_compact L H hY) hε t x v‖^2+
          ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
            (freshObservationRegion_compact L H hY) hε t i x) v‖^2) := by
  obtain ⟨B,hB,K,hK,hbound⟩ := observed_generators_common_control P (fun _ => 1)
  let n := Fintype.card ↥(observedGenerators N)
  refine ⟨B,hB,(n : ℝ)*K,mul_nonneg (Nat.cast_nonneg _) hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨_hex,hqN,_ht,_a,_hqa,_hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,?_⟩
  intro w hw s hs ε Y H hε hY hre hlo him t x v
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  let Q := K*((integerCompactDistortion L H)^t)^2*
    (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
      ‖fixedPrimeStack N w (freshObservationRegion_compact L H hY) hε t x v‖^2+
      ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
        (freshObservationRegion_compact L H hY) hε t i x) v‖^2)
  have hterm (γ : ↥(observedGenerators N)) :
      ‖AsymptoticCongruenceDefect.operator γ.val hs hε t x v‖^2≤Q := by
    obtain ⟨_hqN,hγ⟩ := hbound γ C hBC q hqGood
    have hh := hγ w hw hs hε hY hre hlo him t x v
    simpa only [map_one,mul_one,compactAction_congruence] using hh
  rw [PiLp.norm_sq_eq_of_L2]
  have hsum := Finset.sum_le_sum (fun γ (_ : γ∈(Finset.univ : Finset ↥(observedGenerators N))) => hterm γ)
  exact hsum.trans_eq (by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    dsimp only [Q,n]
    ring)

#print axioms full_gamma0_generator_stack_bound
#print axioms QuantitativeEulerDensityGenerators.observedGenerators_closure
end QuantitativeEulerEndpointPrepared
