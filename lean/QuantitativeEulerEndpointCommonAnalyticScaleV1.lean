module

public import QuantitativeEulerEndpointCommonAnalyticErrorV1
public import QuantitativeEulerEndpointHorizonTraceScaleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight QuantitativeHolomorphic QuantitativeHolomorphic.Schedule

/-- A double-exponential horizon coefficient times inverse sqrt(weight)
is paid at the same endpoint scale as finite-branch trace comparison. -/
theorem horizon_sqrt_error_at_scale {D c : ℝ} (hD : 0≤D) (n h : ℕ) (hh : 0<h)
    (hlog : 32≤Real.log (Real.log (h+1:ℝ)))
    (hn : (4:ℝ)^n≤(Real.log (observationScale c (h+1)))^2)
    (hscale : D*c^2≤1/2) :
    Real.exp (Real.exp (D*(4:ℝ)^n))*(Real.sqrt (2*h+2:ℝ))⁻¹≤Real.exp (-Real.log (h+1:ℝ)/4) := by
  have hm := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hD))
  have hp := mul_le_mul hm (inverse_sqrt_weight_le_trace_power h)
    (by positivity : 0≤(Real.sqrt (2*h+2:ℝ))⁻¹) (Real.exp_pos _).le
  have he : Real.exp (Real.log (observationScale c (h+1)))=observationScale c (h+1) :=
    Real.exp_log (Real.exp_pos _)
  rw [double_exp_mul_trace_power,he] at hp
  exact hp.trans (bridgeErrorThird_at_scale (by exact_mod_cast (show 1<h+1 by omega)) hlog hscale)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- All actual analytic errors are controlled at a single horizon and scale. -/
theorem exists_horizon_analytic_scale {K : ℝ} (hK : 0≤K) :
    ∃ C D : ℝ,0≤C ∧ 0≤D ∧ ∀ n h : ℕ,∀ c : ℝ,0<h →
      32≤Real.log (Real.log (h+1:ℝ)) →
      (4:ℝ)^n≤(Real.log (observationScale c (h+1)))^2 → D*c^2≤1/2 →
      let s := Real.exp ((K+1)*(4:ℝ)^n)
      retainedTraceError A P s h+weightedTraceError A P s h≤
        C/(4:ℝ)^n+2*Real.exp (-Real.log (h+1:ℝ)/4) := by
  obtain ⟨C,D,hC,hD,herr⟩ := exists_horizon_analytic_error A P hK
  refine ⟨C,D,hC,hD,?_⟩
  intro n h c hh hlog hn hscale s
  have hp := horizon_sqrt_error_at_scale hD n h hh hlog hn hscale
  have he := herr n h
  dsimp only at he
  nlinarith only [hp,he]

#print axioms horizon_sqrt_error_at_scale
#print axioms exists_horizon_analytic_scale
end QuantitativeEulerEndpointCommonReconstruction
