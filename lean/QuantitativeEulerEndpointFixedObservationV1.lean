module

public import QuantitativeEulerEndpointFixedRecoveryV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators
open QuantitativeEulerDiamondDecode QuantitativeEulerDiamondPolynomial
open AsymptoticFreshCompactDefects AsymptoticRationalBranches AsymptoticRegularBranchFamily
open AsymptoticRegularObservationRows AsymptoticObservationStack
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- Every individual row at a fixed prime is controlled by the ORIGINAL
fixed-prime average and the ACTUAL fresh-prime stack, with all correction
words bounded. Constants precede the fresh prime and analytic cutoffs. -/
theorem fixed_prime_individual_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ℓ∣N) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (j : Fin (ℓ-1)) (w : ℂ) (_hw : w*w=1)
        {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      ‖(w • compact (matrixBranch N ℓ (NeZero.pos N) hℓ j) hs hε t x-
        compact identityBranch hs hε t x) v‖^2≤
      18*‖twist N ℓ (NeZero.pos N) (Fact.out : ℓ.Prime).pos w
        (inverseRegion_compact ℓ hs) hε t x v‖^2+
      K*((integerCompactDistortion L H)^t)^2*
        (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
          ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
            (freshObservationRegion_compact L H hY) hε t i x) v‖^2) := by
  obtain ⟨B,hB,K,hK,hbound⟩ := fixed_prime_corrections_stack_bound P ℓ hℓ
    (primeInverse ℓ) (Polynomial.aeval (primeX ℓ) (correctionPolynomial ℓ))
  refine ⟨B,hB,2*K,mul_nonneg (by norm_num) hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := hbound C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro j w hw s hs ε Y H hε hY hre hlo him t x v
  have hrec := fixed_prime_residual_squared N ℓ (NeZero.pos N) hℓ w j hs hε t x v
  have hc := mul_le_mul_of_nonneg_left
    (hqbound j w hw hs hε hY hre hlo him t x v) (by norm_num : (0 : ℝ)≤2)
  exact (hrec.trans (add_le_add (le_refl _) hc)).trans_eq (by ring)

#print axioms fixed_prime_individual_stack_bound
end QuantitativeEulerEndpointPrepared
