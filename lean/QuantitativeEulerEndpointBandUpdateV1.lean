module

public import QuantitativeEulerEndpointUpdateMatrixV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBandExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic UpperHalfPlane MeasureTheory Polynomial
open QuantitativeEulerEndpointRegularBase QuantitativeEulerEndpointPolynomialExpression
open QuantitativeEulerEndpointUpdateExpression

variable {ε : ℝ} (hε : 0<ε) (H : ℝ)
local notation "s₀" => region (QuantitativeEulerEndpointBandCorner.ambient (ε:=ε) H)
local notation "hs₀" => region_measurable (QuantitativeEulerEndpointBandCorner.ambient_compact hε H)
local notation "p" => QuantitativeEulerEndpointBandCorner.projection hε H
local notation "hp" => QuantitativeEulerEndpointBandCorner.projection_isStarProjection hε H
local notation "𝔄" => QuantitativeEulerEndpointSubcorner.Subcorner action_measurable s₀ hs₀ p hp
local notation "ρ" => QuantitativeEulerEndpointSubcorner.representation action_measurable s₀ hs₀ p hp

theorem regular_update_representation (a g : 𝔄) (ea eg : Expression)
    (ha : ∀ x : Base,regularSum ea x=ρ a x) (hg : ∀ x : Base,regularSum eg x=ρ g x)
    (n : ℕ) (x : Base) :
    regularSum (updateExpression (unitExpression ε H) ea eg n) x=
      ρ (QuantitativeEulerEndpointSoftUpdate.update a (a*g*a) n) x := by
  rw [regular_update,unit_representation hε H,ha,hg]
  exact (map_update (pointRepresentation hε H x) (pointRepresentation_mul hε H x) a g n).symm

/-- Exact finite expression for the actual update in its original corner,
including the sharpening polynomial and its constant coefficient. -/
theorem regular_sharpened_representation (a g : 𝔄) (ea eg : Expression)
    (ha : ∀ x : Base,regularSum ea x=ρ a x) (hg : ∀ x : Base,regularSum eg x=ρ g x)
    (n : ℕ) (q : ℝ[X]) (x : Base) :
    regularSum (sharpenedExpression (unitExpression ε H) ea eg n q) x=
      ρ (aeval (QuantitativeEulerEndpointSoftUpdate.update a (a*g*a) n) q) x :=
  regular_polynomial_representation hε H _ _
    (regular_update_representation hε H a g ea eg ha hg n) q x

theorem holomorphic_sharpened (u a g : Expression) (n : ℕ) (q : ℝ[X]) (m : ℕ) :
    holomorphicSum (sharpenedExpression u a g n q) m=
      aeval (cornerUpdate (holomorphicSum u m) (holomorphicSum a m) (holomorphicSum g m) n) q*
        holomorphicSum u m := by
  rw [sharpenedExpression,holomorphic_cornerPolynomial,holomorphic_update]

#print axioms regular_sharpened_representation
#print axioms holomorphic_sharpened
end QuantitativeEulerEndpointBandExpression
