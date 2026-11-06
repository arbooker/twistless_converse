module

public import QuantitativeEulerEndpointTraceScaleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTraceMass
open MeasureTheory UpperHalfPlane AsymptoticUnweightedKernel AsymptoticFiniteBranch
open AsymptoticRegularTrace QuantitativeHolomorphic QuantitativeHolomorphic.Schedule
open QuantitativeEulerEndpointBandExpression QuantitativeEulerEndpointRegularBase
open scoped Classical

variable {ε : ℝ} (hε : 0<ε) (H₀ : ℝ) (n : ℕ)
local notation "H" => H₀*(4:ℝ)^n
local notation "hs₀" => QuantitativeEulerEndpointBandCorner.ambient_compact hε H
local notation "s₀" => region (QuantitativeEulerEndpointBandCorner.ambient (ε:=ε) H)
local notation "p" => QuantitativeEulerEndpointBandCorner.projection hε H
local notation "hp" => QuantitativeEulerEndpointBandCorner.projection_isStarProjection hε H
local notation "𝔄" => QuantitativeEulerEndpointSubcorner.Subcorner action_measurable s₀ (region_measurable hs₀) p hp
local notation "ρ" => QuantitativeEulerEndpointSubcorner.representation action_measurable s₀ (region_measurable hs₀) p hp
local notation "τ" => QuantitativeEulerEndpointSubcorner.rootedTrace action_measurable s₀ (region_measurable hs₀) p hp measure (region_finite hs₀)

/-- The original band filter's physical trace approaches its regular rooted
trace at an explicit power rate at the chosen double-logarithmic scale. -/
theorem subcorner_scaled_trace_bound {K a : ℝ} (hK : 0≤K) (hH₀ : 0<H₀)
    (A : 𝔄) (e : Expression) (he : ∀ x : Base,regularSum e x=ρ A x)
    (hm : ExpressionMatrixBound e (Real.exp (Real.exp (K*(4:ℝ)^n))))
    (hf : expressionBound e≤Real.exp (Real.exp (K*(4:ℝ)^n)))
    (h : ℕ) (hh : 0<h)
    (hs : 1≤Real.log (observationScale a (h+1)))
    (hlog : 32≤Real.log (Real.log (h+1:ℝ)))
    (hn : (4:ℝ)^n≤(Real.log (observationScale a (h+1)))^2)
    (hscale : (geometryGrowthCoefficient+29+traceGeometryConstant K H₀ ε)*a^2≤1/2)
    (hphys : holomorphicSum (unitExpression ε H) (h+1)*holomorphicSum e (h+1)=holomorphicSum e (h+1) ∧
      holomorphicSum e (h+1)*holomorphicSum (unitExpression ε H) (h+1)=holomorphicSum e (h+1)) :
    |liftedTrace h hε (holomorphicSum e (h+1))/(2*h+2:ℕ)-τ A/(4*Real.pi)|≤
      Real.exp (-Real.log (h+1:ℝ)/4) := by
  have hg := wide_trace_at_scale hK hH₀ hε n h hh hs hlog hn hscale
  exact (subcorner_trace_bound hε H (by positivity) A e he (by positivity) hm hf h hg.1 hphys).trans hg.2

/-- The discrete horizon loses at most a factor four in geometric contraction. -/
theorem exists_geometric_horizon {X : ℝ} (hX : 1≤X) :
    ∃ n : ℕ,(4:ℝ)^n≤X ∧ ((4:ℝ)^n)⁻¹≤4/X := by
  obtain ⟨n,hn,hnext⟩ := exists_nat_pow_near hX (by norm_num : (1:ℝ)<4)
  refine ⟨n,hn,?_⟩
  rw [pow_succ] at hnext
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<4^n) (by linarith : 0<X)).mpr
  nlinarith

/-- A horizon compatible with the trace scale gives the endpoint inverse
log-log contraction, rather than a smaller fractional power. -/
theorem exists_endpoint_horizon {a : ℝ} (h : ℕ)
    (hs : 1≤Real.log (observationScale a (h+1)))
    (hlog : 0≤Real.log (Real.log (h+1:ℝ))) :
    ∃ n : ℕ,(4:ℝ)^n≤(Real.log (observationScale a (h+1)))^2 ∧
      ((4:ℝ)^n)⁻¹≤4/(a^2*Real.log (Real.log (h+1:ℝ))) := by
  obtain ⟨n,hn,hr⟩ := exists_geometric_horizon
    (show 1≤(Real.log (observationScale a (h+1)))^2 by nlinarith)
  refine ⟨n,hn,?_⟩
  simpa only [log_observationScale_sq a (h+1:ℝ) hlog] using hr

#print axioms subcorner_scaled_trace_bound
#print axioms exists_endpoint_horizon
end QuantitativeEulerEndpointTraceMass
