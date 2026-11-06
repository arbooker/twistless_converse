module

public import QuantitativeEulerEndpointWideRowExpressionsV1
public import QuantitativeEulerEndpointBandGramExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane AsymptoticFiniteBranch QuantitativeHolomorphic
open scoped Classical

variable {s : Set ℍ} (hs : IsCompact s) {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H)

include hY hre hlo hhi in
theorem exists_sequence_expression (N : ℕ) (hN : 0<N) (w : ℂ) (t : ℕ)
    (l : List (EligiblePrime N)) :
    ∃ E : ℕ → Expression, ∀ i : Fin l.length,
      (∀ x,regularSum (E i) x=packetSequence N hN w hs hε t l i x) ∧
      expressionBound (E i)≤wideSequenceBound N w R Y H t l i ∧
      ExpressionMatrixBound (E i)
        (4*(1+(wideCompactCutoff (N*l[i.val].val^3:ℕ) R Y H:ℝ))*(N*l[i.val].val^3:ℕ)) := by
  have he (i : Fin l.length) := exists_packet_expression hs hε hY hre hlo hhi
    N l[i.val].val hN w t
  choose e hr hm hb using he
  let E (i : ℕ) : Expression := if h : i<l.length then e ⟨i,h⟩ else []
  refine ⟨E,?_⟩
  intro i
  have hEi : E i=e i := dite_eq_left i.isLt
  rw [hEi]
  refine ⟨?_,?_,hb i⟩
  · intro x
    rw [hr]
    unfold packetSequence
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt),List.getElem_map]
  · unfold wideSequenceBound
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt),List.getElem_map]
    exact hm i

include hY hre hlo hhi in
/-- Actual original packet rows admit one normalized Gram expression with
coefficient mass at most one; no branch-count premise is needed. -/
theorem exists_normalized_sequence_expression (N : ℕ) (hN : 0<N) (w : ℂ) (t : ℕ)
    (l : List (EligiblePrime N)) (H₀ : ℝ) :
    ∃ E : ℕ → Expression,
      (∀ i : Fin l.length,∀ x,regularSum (E i) x=packetSequence N hN w hs hε t l i x) ∧
      expressionBound (QuantitativeEulerEndpointNormalizedExpression.gram
        (QuantitativeEulerEndpointBandExpression.unitExpression ε H₀) E
        (wideSequenceBound N w R Y H t l) l.length)≤1 ∧
      (∀ i : Fin l.length,ExpressionMatrixBound (E i)
        (4*(1+(wideCompactCutoff (N*l[i.val].val^3:ℕ) R Y H:ℝ))*(N*l[i.val].val^3:ℕ))) := by
  obtain ⟨E,hE⟩ := exists_sequence_expression hs hε hY hre hlo hhi N hN w t l
  refine ⟨E,fun i => (hE i).1,?_,fun i => (hE i).2.2⟩
  exact QuantitativeEulerEndpointNormalizedExpression.gram_mass
    (le_of_eq (QuantitativeEulerEndpointBandExpression.unit_mass ε H₀)) l.length
    (fun i => (hE i).2.1)

#print axioms exists_sequence_expression
#print axioms exists_normalized_sequence_expression
end QuantitativeEulerEndpointPrepared
