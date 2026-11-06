module

public import QuantitativeEulerEndpointPolynomialExpressionV1
public import QuantitativeEulerEndpointBandCornerV1
public import AsymptoticFiniteBranchCornersV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBandExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic UpperHalfPlane MeasureTheory Polynomial
open AsymptoticHyperbolicArea QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointPolynomialExpression

/-- The unit of the ACTUAL source subcorner is its band projection. -/
def unitExpression (ε H : ℝ) : Expression :=
  [AsymptoticFiniteBranch.corner (terminal ε\terminal H)
    ((terminal_measurable ε).diff (terminal_measurable H))]

theorem unit_mass (ε H : ℝ) : expressionBound (unitExpression ε H)=1 := by
  simp [unitExpression,expressionBound,AsymptoticFiniteBranch.corner]

theorem unit_matrix (ε H : ℝ) : ExpressionMatrixBound (unitExpression ε H) 1 := by
  intro b hb
  have hb' : b=AsymptoticFiniteBranch.corner (terminal ε\terminal H)
      ((terminal_measurable ε).diff (terminal_measurable H)) := by simpa only [unitExpression,List.mem_singleton] using hb
  subst b
  refine ⟨1,integerAction_one,?_⟩
  intro i j
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

theorem unit_regular (ε H : ℝ) (x : ℍ) :
    regularSum (unitExpression ε H) x=AsymptoticOrbitDiagonal.corner (terminal ε\terminal H) x := by
  simp only [unitExpression,regularSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,regular_corner]

theorem unit_holomorphic (ε H : ℝ) (m : ℕ) :
    holomorphicSum (unitExpression ε H) m=AsymptoticRegionL2.projection volume
      (terminal ε\terminal H) ((terminal_measurable ε).diff (terminal_measurable H)) := by
  simp only [unitExpression,holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,holomorphic_corner]

variable {ε : ℝ} (hε : 0<ε) (H : ℝ)
local notation "s₀" => region (QuantitativeEulerEndpointBandCorner.ambient (ε:=ε) H)
local notation "hs₀" => region_measurable (QuantitativeEulerEndpointBandCorner.ambient_compact hε H)
local notation "p" => QuantitativeEulerEndpointBandCorner.projection hε H
local notation "hp" => QuantitativeEulerEndpointBandCorner.projection_isStarProjection hε H
local notation "𝔄" => QuantitativeEulerEndpointSubcorner.Subcorner action_measurable s₀ hs₀ p hp
local notation "ρ" => QuantitativeEulerEndpointSubcorner.representation action_measurable s₀ hs₀ p hp

def pointRepresentation (x : Base) : 𝔄 →ₗ[ℝ] (RegularSpace →L[ℂ] RegularSpace) :=
  (LinearMap.proj x).comp ρ

theorem pointRepresentation_mul (x : Base) (a b : 𝔄) :
    pointRepresentation hε H x (a*b)=pointRepresentation hε H x a*pointRepresentation hε H x b := rfl

theorem unit_representation (x : Base) : regularSum (unitExpression ε H) x=ρ 1 x :=
  unit_regular ε H x

theorem regular_polynomial_representation (a : 𝔄) (e : Expression)
    (he : ∀ x : Base, regularSum e x=ρ a x) (q : ℝ[X]) (x : Base) :
    regularSum (cornerPolynomial (unitExpression ε H) e q) x=ρ (aeval a q) x := by
  rw [regular_cornerPolynomial,he,unit_representation hε H]
  exact (QuantitativeEulerEndpointCornerPolynomial.map_aeval_corner
    (pointRepresentation hε H x) (pointRepresentation_mul hε H x) a q).symm

#print axioms unit_matrix
#print axioms unit_holomorphic
#print axioms regular_polynomial_representation
end QuantitativeEulerEndpointBandExpression
