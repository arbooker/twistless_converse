module

public import QuantitativeEulerEndpointSubcornerPhysicalTraceV1
public import QuantitativeHolomorphicGrowingScaledTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTraceMass
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule

/-- Concrete cost of the wider band and its matrix denominator bound. -/
def traceGeometryConstant (K H₀ ε : ℝ) : ℝ := K+2*H₀+2*ε⁻¹+8

theorem traceGeometryConstant_nonneg {K H₀ ε : ℝ} (hK : 0≤K) (hH : 0≤H₀) (hε : 0<ε) :
    0≤traceGeometryConstant K H₀ ε := by unfold traceGeometryConstant; positivity

/-- The actual mass, enlarged height, reciprocal lower cutoff and denominator
bound have one explicit double-exponential envelope, uniform in horizon. -/
theorem wide_trace_geometry {K H₀ ε R : ℝ} (hK : 0≤K) (hH : 0≤H₀) (hε : 0<ε) (hR : 1≤R) :
    let B := Real.exp (Real.exp (K*R))
    let C := traceGeometryConstant K H₀ ε
    B*(2*(H₀*R)+2)≤Real.exp (Real.exp (C*R)) ∧
    2*(H₀*R)≤Real.exp (Real.exp (C*R)) ∧
    (ε/2)⁻¹≤Real.exp (Real.exp (C*R)) ∧ B≤Real.exp (Real.exp (C*R)) := by
  let C := traceGeometryConstant K H₀ ε
  let t := 2*(H₀*R)+2
  have hR0 : 0≤R := by linarith
  have hi : 0≤ε⁻¹ := (inv_pos.mpr hε).le
  have ht0 : 0≤t := by dsimp [t]; positivity
  have hC : K≤C := by dsimp [C,traceGeometryConstant]; linarith
  have ht : K*R+t≤C*R := by dsimp [C,t,traceGeometryConstant]; nlinarith [mul_nonneg hi hR0]
  have hy : 2*ε⁻¹≤C*R := by
    have hh : 2*ε⁻¹≤C := by dsimp [C,traceGeometryConstant]; linarith
    have hc : 0≤C := traceGeometryConstant_nonneg hK hH hε
    nlinarith
  have hexp1 : 1≤Real.exp (K*R) := Real.one_le_exp_iff.mpr (mul_nonneg hK hR0)
  have hinner : Real.exp (K*R)+t≤Real.exp (C*R) := calc
    _ ≤ Real.exp (K*R)*(t+1) := by nlinarith
    _ ≤ Real.exp (K*R)*Real.exp t := mul_le_mul_of_nonneg_left (Real.add_one_le_exp t) (Real.exp_pos _).le
    _ = Real.exp (K*R+t) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr ht
  have houter : C*R≤Real.exp (Real.exp (C*R)) := by
    linarith [Real.add_one_le_exp (C*R),Real.add_one_le_exp (Real.exp (C*R))]
  refine ⟨?_,?_,?_,?_⟩
  · calc
      _ ≤ Real.exp (Real.exp (K*R))*Real.exp t := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp t] : t≤Real.exp t) (Real.exp_pos _).le
      _ = Real.exp (Real.exp (K*R)+t) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hinner
  · dsimp only [t] at ht
    nlinarith [mul_nonneg hK hR0]
  · have he : (ε/2)⁻¹=2*ε⁻¹ := by rw [inv_div]; ring
    rw [he]
    exact hy.trans houter
  · exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC hR0))

/-- At the double-logarithmic scale the actual enlarged-band trace error is
small, and the required separation condition is automatically satisfied. -/
theorem wide_trace_at_scale {K H₀ ε a : ℝ} (hK : 0≤K) (hH : 0<H₀) (hε : 0<ε)
    (n h : ℕ) (hh : 0<h)
    (hs : 1≤Real.log (observationScale a (h+1)))
    (hlog : 32≤Real.log (Real.log (h+1:ℝ)))
    (hn : (4:ℝ)^n≤(Real.log (observationScale a (h+1)))^2)
    (hscale : (geometryGrowthCoefficient+29+traceGeometryConstant K H₀ ε)*a^2≤1/2) :
    let H := H₀*(4:ℝ)^n
    let B := Real.exp (Real.exp (K*(4:ℝ)^n))
    (h+1:ℝ)^(-(1/3:ℝ))*(B*(2*H+2))≤1 ∧
    B*uniformRetainedTraceError (B*(2*H+2)) (ε/2) (2*H) h (periodizationSet (ε/2) (2*H)).card≤
      Real.exp (-Real.log (h+1:ℝ)/4) := by
  have hc := traceGeometryConstant_nonneg hK hH.le hε
  have hg := wide_trace_geometry hK hH.le hε (one_le_pow₀ (by norm_num : (1:ℝ)≤4) : 1≤(4:ℝ)^n)
  have hm : Real.exp (Real.exp (traceGeometryConstant K H₀ ε*(4:ℝ)^n))≤
      Real.exp (Real.exp (traceGeometryConstant K H₀ ε*(Real.log (observationScale a (h+1)))^2)) :=
    Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hc))
  exact growing_retained_trace_at_scale h hh (by positivity) (by positivity) (by positivity)
    (Real.exp_pos _).le hc hs hlog hscale
    (hg.1.trans hm) (hg.2.1.trans hm) (hg.2.2.1.trans hm) (hg.2.2.2.trans hm)

#print axioms wide_trace_geometry
#print axioms wide_trace_at_scale
end QuantitativeEulerEndpointTraceMass
