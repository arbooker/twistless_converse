module

public import QuantitativeEulerEndpointCommonTraceGeometryV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- The actual common cutoff geometry pays the canonical periodization
error and finite-weight separation at a double-logarithmic block horizon.
The constant is chosen before horizon and weight. -/
theorem exists_horizon_trace_scale {K a : ℝ} (hK : 0≤K) (ha : 0≤a) :
    ∃ C : ℝ,0≤C ∧ ∀ n h : ℕ,∀ c : ℝ,0<h →
      1≤Real.log (observationScale c (h+1)) →
      32≤Real.log (Real.log (h+1:ℝ)) →
      (4:ℝ)^n≤(Real.log (observationScale c (h+1)))^2 →
      (geometryGrowthCoefficient+29+C)*c^2≤1/2 →
      let s := Real.exp ((K+1)*(4:ℝ)^n)
      let M := Real.exp (Real.exp (a*(4:ℝ)^n))
      let Y := lowerHeight A P s
      let H := Real.exp (16*s)
      (h+1:ℝ)^(-(1/3:ℝ))*(M*(H+2))≤1 ∧
        M*uniformRetainedTraceError (M*(H+2)) Y H h (periodizationSet Y H).card≤
          Real.exp (-Real.log (h+1:ℝ)/4) := by
  obtain ⟨C,hC,hgeom⟩ := exists_horizon_trace_geometry A P hK ha
  refine ⟨C,hC,?_⟩
  intro n h c hh hs hlog hn hscale s M Y H
  have hg := hgeom n
  have hm : Real.exp (Real.exp (C*(4:ℝ)^n))≤
      Real.exp (Real.exp (C*(Real.log (observationScale c (h+1)))^2)) :=
    Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hC))
  exact growing_retained_trace_at_scale h hh (by positivity) (lowerHeight_pos A P s)
    (Real.exp_pos _) (Real.exp_pos _).le hC hs hlog hscale
    (hg.1.trans hm) (hg.2.1.trans hm) (hg.2.2.1.trans hm) (hg.2.2.2.trans hm)

#print axioms exists_horizon_trace_scale
end QuantitativeEulerEndpointCommonReconstruction
