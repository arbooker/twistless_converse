module

public import QuantitativeEulerEndpointGeneratorRowsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open AsymptoticObservationStack
open scoped Classical MatrixGroups

/-- The whole fixed Gamma1 detector, not just one selected generator,
is bounded by the SAME actual fresh-prime stack on the SAME region. -/
theorem good_prime_full_generator_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (q : ℕ) [Fact q.Prime] (hqGood : P.Good q) :
    ∃ hqN : ¬q∣N, ∀ (w : ℂ) (_hw : w*w=1)
      {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
      (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
    let L := generatorTransportConstant P*(q : ℝ)^4
    ‖stack (fun γ : Generator N => AsymptoticCongruenceDefect.operator γ.val hs hε t x) v‖^2≤
    (200*(Fintype.card (Generator N) : ℝ))*((integerCompactDistortion L H)^t)^2*
      (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
        ‖stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
          (freshObservationRegion_compact L H hY) hε t j x) v‖^2) := by
  obtain ⟨hqN,h⟩ := good_prime_generator_stack_bound P q hqGood
  refine ⟨hqN,?_⟩
  intro w hw s hs ε Y H hε hY hre hlo him t x v
  rw [PiLp.norm_sq_eq_of_L2]
  have hh := Finset.sum_le_sum (fun γ (_ : γ∈(Finset.univ : Finset (Generator N))) =>
    h γ w hw hs hε hY hre hlo him t x v)
  exact hh.trans_eq (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring)

#print axioms good_prime_full_generator_stack_bound
end QuantitativeEulerEndpointPrepared
