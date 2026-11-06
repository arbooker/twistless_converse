module

public import QuantitativeEulerEndpointTraceBandV1
public import QuantitativeHolomorphicQuantifiedTraceV1
public import QuantitativeHolomorphicGrowingPeriodizationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTraceMass
open MeasureTheory UpperHalfPlane AsymptoticUnweightedKernel AsymptoticFiniteBranch
open AsymptoticRegularTrace QuantitativeHolomorphic QuantitativeHolomorphic.Schedule
open QuantitativeEulerEndpointBandExpression QuantitativeEulerEndpointRegularBase
open scoped Classical

variable {ε : ℝ} (hε : 0<ε) (H : ℝ)
local notation "hs₀" => QuantitativeEulerEndpointBandCorner.ambient_compact hε H
local notation "s₀" => region (QuantitativeEulerEndpointBandCorner.ambient (ε:=ε) H)
local notation "p" => QuantitativeEulerEndpointBandCorner.projection hε H
local notation "hp" => QuantitativeEulerEndpointBandCorner.projection_isStarProjection hε H
local notation "𝔄" => QuantitativeEulerEndpointSubcorner.Subcorner action_measurable s₀ (region_measurable hs₀) p hp
local notation "ρ" => QuantitativeEulerEndpointSubcorner.representation action_measurable s₀ (region_measurable hs₀) p hp
local notation "τ" => QuantitativeEulerEndpointSubcorner.rootedTrace action_measurable s₀ (region_measurable hs₀) p hp measure (region_finite hs₀)

/-- Exact band support is automatic for a represented element of the original
regular subcorner; no positivity premise is needed. -/
theorem represented_band_support (a : 𝔄) (e : Expression) (he : ∀ x : Base,regularSum e x=ρ a x) (x : ℍ) :
    regularSum (unitExpression ε H) x*regularSum e x=regularSum e x ∧
      regularSum e x*regularSum (unitExpression ε H) x=regularSum e x := by
  rw [he x,unit_representation hε H]
  exact ⟨congrArg (fun b : 𝔄 => ρ b x) (one_mul a),congrArg (fun b : 𝔄 => ρ b x) (mul_one a)⟩

theorem represented_signedTrace (a : 𝔄) (e : Expression) (he : ∀ x : Base,regularSum e x=ρ a x) :
    signedTrace volume (regularSum e)=τ a := by
  change signedTrace volume (regularSum e)=signedTrace volume (fun x : ℍ => ρ a x)
  rw [funext he]

/-- Finite-weight comparison for the SAME represented band filter, with
canonical periodization, coefficient mass and matrix height only. -/
theorem subcorner_trace_bound (hH : 0<H) (a : 𝔄) (e : Expression)
    (he : ∀ x : Base,regularSum e x=ρ a x) {B F : ℝ} (hB : 0≤B)
    (hm : ExpressionMatrixBound e B) (hf : expressionBound e≤F)
    (h : ℕ) (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*(B*(2*H+2))≤1)
    (hphys : holomorphicSum (unitExpression ε H) (h+1)*holomorphicSum e (h+1)=holomorphicSum e (h+1) ∧
      holomorphicSum e (h+1)*holomorphicSum (unitExpression ε H) (h+1)=holomorphicSum e (h+1)) :
    |liftedTrace h hε (holomorphicSum e (h+1))/(2*h+2:ℕ)-τ a/(4*Real.pi)|≤
      F*uniformRetainedTraceError (B*(2*H+2)) (ε/2) (2*H) h (periodizationSet (ε/2) (2*H)).card := by
  have hh := band_expression_trace_bound e hε hH hB hm h hsmall
    (periodizationSet (ε/2) (2*H)) (periodizationSet_far _ _)
    (represented_band_support hε H a e he) hphys
  rw [represented_signedTrace hε H a e he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hf
    (uniformRetainedTraceError_nonneg _ _ (by positivity : 0<ε/2) _ _))

#print axioms represented_signedTrace
#print axioms subcorner_trace_bound
end QuantitativeEulerEndpointTraceMass
