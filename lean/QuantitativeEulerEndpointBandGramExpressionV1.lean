module

public import QuantitativeEulerEndpointNormalizedExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBandExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic UpperHalfPlane MeasureTheory
open QuantitativeEulerEndpointRegularBase AsymptoticRegularTrace

variable {ε : ℝ} (hε : 0<ε) (H : ℝ)
local notation "s₀" => region (QuantitativeEulerEndpointBandCorner.ambient (ε:=ε) H)
local notation "hs₀" => region_measurable (QuantitativeEulerEndpointBandCorner.ambient_compact hε H)
local notation "p" => QuantitativeEulerEndpointBandCorner.projection hε H
local notation "hp" => QuantitativeEulerEndpointBandCorner.projection_isStarProjection hε H
local notation "ρ" => QuantitativeEulerEndpointSubcorner.representation action_measurable s₀ hs₀ p hp

variable (B : ℕ → Base → RegularSpace →L[ℂ] RegularSpace)
  (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h))
  (hcB : ∀ i, Covariant (B i)) (C : ℕ → ℝ) (hC : ∀ i x, ‖B i x‖≤C i)
local notation "NB" => QuantitativeEulerEndpointNormalizedRows.row action_measurable s₀ hs₀ p B C
local notation "NC" => QuantitativeEulerEndpointNormalizedRows.bound C
local notation "hmNB" => QuantitativeEulerEndpointNormalizedRows.row_measurable action_measurable s₀ hs₀ p B hmB C
local notation "hcNB" => QuantitativeEulerEndpointNormalizedRows.row_covariant action_measurable s₀ hs₀ p B hcB C
local notation "hnNB" => QuantitativeEulerEndpointNormalizedRows.row_norm action_measurable s₀ hs₀ p hp B C hC
local notation "hsNB" => QuantitativeEulerEndpointNormalizedRows.row_source action_measurable s₀ hs₀ p hp B C

theorem regular_normalized_gram (E : ℕ → Expression) (n : ℕ)
    (hE : ∀ i : Fin n,∀ x : Base,regularSum (E i) x=B i x) (x : Base) :
    regularSum (QuantitativeEulerEndpointNormalizedExpression.gram (unitExpression ε H) E C n) x=
      ρ (QuantitativeEulerEndpointBlockGram.gramSum action_measurable s₀ hs₀ p hp
        (NB n) (hmNB n) (hcNB n) (NC n) (hnNB n) (hsNB n) n) x := by
  rw [QuantitativeEulerEndpointNormalizedExpression.regular_gram,
    QuantitativeEulerEndpointBlockGram.representation_gramSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hE i,unit_regular]
  rfl

#print axioms regular_normalized_gram
end QuantitativeEulerEndpointBandExpression
