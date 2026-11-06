module

public import QuantitativeEulerEndpointWordHeightV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane CongruenceSubgroup QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open AsymptoticCongruenceLabels AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open AsymptoticObservationStack
open scoped Classical MatrixGroups

/-- Every fixed Gamma1 word with an integral right multiplier is controlled
by the actual fresh-prime stack. Word length and suffix height are selected
BEFORE the fresh prime and every analytic cutoff, not afterward. -/
theorem gamma1_fixed_word_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (γ : SL(2,ℤ)) (hγ : γ∈Gamma1 N) (β : SL(2,ℤ)) :
    ∃ B : ℝ, 1≤B ∧ ∃ m : ℕ,
      ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (w : ℂ) (_hw : w*w=1)
        {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      let L := (2*generatorTransportConstant P*B)*(q : ℝ)^4
      ‖compactAction hs hε t x
        ((symbol (integralLabel γ)-1)*symbol (integralLabel β)) v‖^2≤
      (200*(m : ℝ)^2)*((integerCompactDistortion L H)^t)^2*
        (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
          ‖stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
            (freshObservationRegion_compact L H hY) hε t j x) v‖^2) := by
  obtain ⟨W,hW,hexp⟩ := gamma1_compact_generator_expansion N γ hγ
  let B := wordTransportHeight W β
  have hB : 1≤B := wordTransportHeight_one_le W β
  refine ⟨B,hB,W.length,?_⟩
  intro q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := good_prime_generator_right_stack_bound P q hqGood
  refine ⟨hqN,?_⟩
  intro w hw s hs ε Y H hε hY hre hlo him t x v
  let L := (2*generatorTransportConstant P*B)*(q : ℝ)^4
  let K := 200*((integerCompactDistortion L H)^t)^2*
    (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
      ‖stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
        (freshObservationRegion_compact L H hY) hε t j x) v‖^2)
  have hterm (i : Fin W.length) :
      ‖compactAction hs hε t x
        ((symbol (integralLabel (W.get i).1)-1)*symbol (integralLabel ((W.get i).2*β))) v‖^2≤K := by
    obtain ⟨hb,hb'⟩ := wordTransportHeight_bounds W β i
    rcases hW (W.get i) (List.get_mem W i) with hpos | hneg
    · exact hqbound ⟨_,hpos⟩ ((W.get i).2*β) B (zero_le_one.trans hB) hb
        w hw hs hε hY hre hlo him t x v
    · rw [inverse_letter_norm (W.get i).1 ((W.get i).2*β) hs hε t x v]
      exact hqbound ⟨_,hneg⟩ ((W.get i).1*((W.get i).2*β)) B (zero_le_one.trans hB) hb'
        w hw hs hε hY hre hlo him t x v
  have hsum := finite_sum_squared_bound
    (fun i : Fin W.length => compactAction hs hε t x
      ((symbol (integralLabel (W.get i).1)-1)*symbol (integralLabel ((W.get i).2*β))) v) K hterm
  rw [hexp (symbol (integralLabel β)) hs hε t x,
    ←List.ofFn_getElem_eq_map,List.sum_ofFn,_root_.sum_apply]
  simp only [integralLabel.map_mul,symbol.map_mul,Fintype.card_fin] at hsum
  exact hsum.trans_eq (by dsimp only [K]; ring)

#print axioms gamma1_fixed_word_stack_bound
end QuantitativeEulerEndpointPrepared
