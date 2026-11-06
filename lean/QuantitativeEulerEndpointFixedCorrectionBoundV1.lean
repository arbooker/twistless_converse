module

public import QuantitativeEulerEndpointFixedCorrectionV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane CongruenceSubgroup QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open AsymptoticCongruenceLabels AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open AsymptoticObservationStack
open scoped Classical MatrixGroups

/-- Both literal fixed-prime correction terms are controlled by the actual
fresh-prime stack. The same constants and region work for every fixed-prime
residue. In particular E and F may be the actual inverse and correction
polynomials evaluated at the fixed prime's translation. -/
theorem fixed_prime_corrections_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ℓ∣N) (E F : Ring) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (j : Fin (ℓ-1)) (w : ℂ) (_hw : w*w=1)
        {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      ‖compactAction hs hε t x (primeCongruenceCorrection N ℓ (NeZero.pos N) hℓ w j*E+
        primePeriodCorrection N ℓ (NeZero.pos N) hℓ w j*F) v‖^2≤
      K*((integerCompactDistortion L H)^t)^2*
        (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
          ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
            (freshObservationRegion_compact L H hY) hε t i x) v‖^2) := by
  let I := Option (Fin (ℓ-1))
  let γ : Fin (ℓ-1) × I → SL(2,ℤ) := fun p => fixedCorrectionLetter N ℓ hℓ p.1 p.2
  let M : Fin (ℓ-1) × I → Ring := fun p =>
    fixedCorrectionMultiplier N ℓ (NeZero.pos N) hℓ E F p.1 p.2
  obtain ⟨B,hB,K,hK,hbound⟩ := gamma1_finite_multiplier_stack_bound P γ
    (fun p => fixedCorrectionLetter_mem N ℓ hℓ p.1 p.2) M
  let K₀ := (Fintype.card I : ℝ)^2*K
  refine ⟨B,hB,K₀,mul_nonneg (sq_nonneg _) hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := hbound C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro j w hw s hs ε Y H hε hY hre hlo him t x v
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  let Q := ((integerCompactDistortion L H)^t)^2*
    (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
      ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
        (freshObservationRegion_compact L H hY) hε t i x) v‖^2)
  let u : I → Space := fun i => compactAction hs hε t x
    ((symbol (integralLabel (γ (j,i)))-1)*M (j,i)) v
  have hu (i : I) : ‖u i‖^2≤K*Q :=
    (hqbound (j,i) w hw hs hε hY hre hlo him t x v).trans_eq (mul_assoc _ _ _)
  have hsum := finite_sum_squared_bound u (K*Q) hu
  have hwNorm : ‖w‖^2=1 := by
    simpa only [norm_mul,norm_one,pow_two] using congrArg norm hw
  rw [compact_fixedCorrection_sum,norm_smul,mul_pow,hwNorm,one_mul]
  exact hsum.trans_eq (by dsimp only [K₀,Q]; ring)

#print axioms fixed_prime_corrections_stack_bound
end QuantitativeEulerEndpointPrepared
