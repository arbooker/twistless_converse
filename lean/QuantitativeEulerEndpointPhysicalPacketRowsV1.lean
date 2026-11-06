module

public import QuantitativeEulerEndpointWideRowExpressionsV1
public import QuantitativeEulerEndpointWideSequenceExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane AsymptoticFiniteBranch QuantitativeHolomorphic
open AsymptoticRegularObservationRows AsymptoticCertificateBranches
open scoped Classical

variable {s : Set ℍ} (hs : IsCompact s) {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H)

/-- The original physical twist row, with its exact prime normalization. -/
def originalPacketExpression (N q : ℕ) (hN : 0<N) (hq : 0<q) (w : ℂ) (t : ℕ) : Expression :=
  scaleExpression ((-Real.sqrt (2*(q:ℝ)):ℝ):ℂ)
    (compactFamilyExpression (twistBranches N q hN hq)
      (Sum.elim (fun _ => (1:ℂ)) (fun _ => -w)) hs hε t)

include hY hre hlo hhi in
theorem exists_packet_expression_physical (N q : ℕ) [Fact q.Prime] (hN : 0<N) (w : ℂ) (t : ℕ) :
    ∃ E : Expression,
      (∀ x, regularSum E x=packetTwistRow N q hN w hs hε t x) ∧
      (∀ m,holomorphicSum E m=holomorphicSum (originalPacketExpression hs hε N q hN (Fact.out : q.Prime).pos w t) m) ∧
      expressionBound E≤widePacketBound N q w R Y H t ∧
      ExpressionMatrixBound E (4*(1+(wideCompactCutoff (N*q^3:ℕ) R Y H:ℝ))*(N*q^3:ℕ)) := by
  obtain ⟨E,hE,hphys,hmass,hmatrix⟩ := exists_twist_expression hs hε hY hre hlo hhi
    N q hN (Fact.out : q.Prime).pos w t
  let a : ℝ := -Real.sqrt (2*(q:ℝ))
  refine ⟨scaleExpression (a:ℂ) E,?_,?_,?_,hmatrix.scale (a:ℂ)⟩
  · intro x
    rw [regularSum_scale,hE,packet_twist_row_eq]
    exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) a (twist N q hN (Fact.out : q.Prime).pos w hs hε t x)).symm
  · intro m
    rw [holomorphicSum_scale,hphys,originalPacketExpression,holomorphicSum_scale]
  · have hq1 : (1:ℝ)≤q := by exact_mod_cast (Fact.out : q.Prime).one_le
    have hsq : Real.sqrt (2*(q:ℝ))≤2*(q:ℝ) := by
      have hh := Real.sqrt_le_sqrt (show 2*(q:ℝ)≤(2*(q:ℝ))^2 by nlinarith)
      simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg (show 0≤2*(q:ℝ) by positivity)] using hh
    rw [expressionBound_scale,Complex.norm_real,Real.norm_eq_abs]
    dsimp only [a]
    rw [abs_neg,abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ (2*(q:ℝ))*wideTwistBound N q w R Y H t := mul_le_mul hsq hmass
        (expressionBound_nonneg _) (by positivity)
      _ = _ := by unfold wideTwistBound widePacketBound wideRowBound; ring

def originalPacketSequenceExpression (N : ℕ) (hN : 0<N) (w : ℂ) (t : ℕ)
    (l : List (EligiblePrime N)) (i : Fin l.length) : Expression :=
  originalPacketExpression hs hε N l[i.val].val hN l[i.val].property.1.pos w t

include hY hre hlo hhi in
theorem exists_sequence_expression_physical (N : ℕ) (hN : 0<N) (w : ℂ) (t : ℕ)
    (l : List (EligiblePrime N)) :
    ∃ E : ℕ → Expression, ∀ i : Fin l.length,
      (∀ x,regularSum (E i) x=packetSequence N hN w hs hε t l i x) ∧
      (∀ m,holomorphicSum (E i) m=holomorphicSum (originalPacketSequenceExpression hs hε N hN w t l i) m) ∧
      expressionBound (E i)≤wideSequenceBound N w R Y H t l i ∧
      ExpressionMatrixBound (E i)
        (4*(1+(wideCompactCutoff (N*l[i.val].val^3:ℕ) R Y H:ℝ))*(N*l[i.val].val^3:ℕ)) := by
  have he (i : Fin l.length) := exists_packet_expression_physical hs hε hY hre hlo hhi
    N l[i.val].val hN w t
  choose e hr hp hm hb using he
  let E (i : ℕ) : Expression := if h : i<l.length then e ⟨i,h⟩ else []
  refine ⟨E,?_⟩
  intro i
  have hEi : E i=e i := dite_eq_left i.isLt
  rw [hEi]
  refine ⟨?_,hp i,?_,hb i⟩
  · intro x
    rw [hr]
    unfold packetSequence
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt),List.getElem_map]
  · unfold wideSequenceBound
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt),List.getElem_map]
    exact hm i

#print axioms exists_packet_expression_physical
#print axioms exists_sequence_expression_physical
end QuantitativeEulerEndpointPrepared
