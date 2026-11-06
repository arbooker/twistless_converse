module

public import QuantitativeEulerEndpointWideSequenceExpressionV1
public import QuantitativeEulerEndpointControlledPacketV1
public import QuantitativeEulerEndpointBandUpdateV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane AsymptoticFiniteBranch QuantitativeHolomorphic
open QuantitativeEulerEndpointRegularBase QuantitativeEulerEndpointBandExpression
open scoped Classical

def packetMatrixBound (N : ℕ) (R Y H : ℝ) (l : List (EligiblePrime N)) : ℝ :=
  ∑ i : Fin l.length,
    4*(1+(wideCompactCutoff (N*l[i.val].val^3:ℕ) R Y H:ℝ))*(N*l[i.val].val^3:ℕ)

theorem packetMatrixBound_nonneg (N : ℕ) (R Y H : ℝ) (l : List (EligiblePrime N)) :
    0≤packetMatrixBound N R Y H l := Finset.sum_nonneg (fun _ _ => by positivity)

variable {s : Set ℍ} (hs : IsCompact s) {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H)
    (N : ℕ) (hN : 0<N) (w : ℂ) (t : ℕ) (l : List (EligiblePrime N)) (H₀ : ℝ)
local notation "hs₀" => QuantitativeEulerEndpointBandCorner.ambient_compact hε H₀
local notation "p" => QuantitativeEulerEndpointBandCorner.projection hε H₀
local notation "hp" => QuantitativeEulerEndpointBandCorner.projection_isStarProjection hε H₀
local notation "ρ" => QuantitativeEulerEndpointSubcorner.representation action_measurable
  (region (QuantitativeEulerEndpointBandCorner.ambient (ε:=ε) H₀)) (region_measurable hs₀) p hp
local notation "C" => wideSequenceBound N w R Y H t l
local notation "hC" => packet_sequence_wide_norm N hN w hs hε hY hre hlo hhi t l
local notation "G" => QuantitativeEulerEndpointControlledPacket.gram hs₀ p hp N hN w hs hε t l C hC

/-- The exact Gram used by the explicitly bounded original prime block has
one finite expression, unit coefficient mass, and explicit matrix height. -/
theorem exists_wide_gram_expression :
    ∃ eg : Expression, (∀ x : Base,regularSum eg x=ρ G x) ∧
      expressionBound eg≤1 ∧ ExpressionMatrixBound eg (8*(packetMatrixBound N R Y H l)^2) := by
  obtain ⟨E,hE⟩ := exists_sequence_expression hs hε hY hre hlo hhi N hN w t l
  let eg := QuantitativeEulerEndpointNormalizedExpression.gram (unitExpression ε H₀) E C l.length
  refine ⟨eg,?_,?_,?_⟩
  · intro x
    exact regular_normalized_gram hε H₀ (packetRows N hN w hs hε t l)
      (fun i => (packetRows_regular N hN w hs hε t l i).1)
      (fun i => (packetRows_regular N hN w hs hε t l i).2)
      C hC E l.length (fun i x => (hE i).1 x) x
  · exact QuantitativeEulerEndpointNormalizedExpression.gram_mass
      (le_of_eq (unit_mass ε H₀)) l.length (fun i => (hE i).2.1)
  · apply QuantitativeEulerEndpointNormalizedExpression.gram_matrix
      (packetMatrixBound_nonneg N R Y H l) (unit_matrix ε H₀) l.length
    intro i
    apply ((hE i).2.2).mono
    unfold packetMatrixBound
    exact Finset.single_le_sum (f:=fun j : Fin l.length =>
      (4*(1+(wideCompactCutoff (N*l[j.val].val^3:ℕ) R Y H:ℝ))*(N*l[j.val].val^3:ℕ)))
      (fun j _ => by positivity) (Finset.mem_univ i)

#print axioms exists_wide_gram_expression
end QuantitativeEulerEndpointPrepared
