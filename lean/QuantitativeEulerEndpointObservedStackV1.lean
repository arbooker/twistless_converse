module

public import QuantitativeEulerEndpointCanonicalStackV1
public import QuantitativeEulerDiamondObservedGeneratorsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open AsymptoticCongruenceLabels AsymptoticRegularObservationRows AsymptoticObservationStack
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- This is the actual observedPrimeMatrix used in observedGenerators_closure,
at the chosen Dirichlet prime for its residue class, with any fixed projective
right multiplier. No substitute Bezout representative is used. -/
theorem observed_matrix_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (g : G) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (w : ℂ) (_hw : w*w=1)
        {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      ‖compactAction hs hε t x
        ((symbol (integralLabel (observedPrimeMatrix N a))-1)*symbol g) v‖^2≤
      K*((integerCompactDistortion L H)^t)^2*
        (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
          ‖twist N (primeLift N a).q (NeZero.pos N) (primeLift N a).prime.pos w
            (freshObservationRegion_compact L H hY) hε t x v‖^2+
          ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
            (freshObservationRegion_compact L H hY) hε t i x) v‖^2) := by
  let : Fact (primeLift N a).q.Prime := ⟨(primeLift N a).prime⟩
  exact fixed_canonical_stack_bound P (primeLift N a).q
    (Nat.not_dvd_of_pos_of_lt (NeZero.pos N) (primeLift N a).large)
    ⟨0,by have h := (primeLift N a).prime.one_lt; omega⟩ g

#print axioms observed_matrix_stack_bound
end QuantitativeEulerEndpointPrepared
