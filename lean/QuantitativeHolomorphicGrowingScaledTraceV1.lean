module

public import QuantitativeHolomorphicGrowingPeriodizationV1
public import QuantitativeHolomorphicGrowingFilterScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

theorem double_exp_mono {K L s : ℝ} (hKL : K≤L) :
    Real.exp (Real.exp (K*s^2))≤Real.exp (Real.exp (L*s^2)) :=
  Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hKL (sq_nonneg _)))

/-- The actual geometric separation and periodized trace costs fit the
double-logarithmic observation scale. Every bound concerns an explicit
matrix/strip/expression parameter, never a presumed trace-error rate. -/
theorem growing_retained_trace_at_scale {D Y H F K a : ℝ} (h : ℕ) (hh : 0<h)
    (hD : 0≤D) (hY : 0<Y) (hH : 0<H) (hF : 0≤F) (hK : 0≤K)
    (hs : 1≤Real.log (observationScale a (h+1)))
    (hL : 32≤Real.log (Real.log (h+1:ℝ)))
    (hscale : (geometryGrowthCoefficient+29+K)*a^2≤1/2)
    (hDM : D≤Real.exp (Real.exp (K*(Real.log (observationScale a (h+1)))^2)))
    (hHM : H≤Real.exp (Real.exp (K*(Real.log (observationScale a (h+1)))^2)))
    (hYM : Y⁻¹≤Real.exp (Real.exp (K*(Real.log (observationScale a (h+1)))^2)))
    (hFM : F≤Real.exp (Real.exp (K*(Real.log (observationScale a (h+1)))^2))) :
    (h+1:ℝ)^(-(1/3:ℝ))*D≤1 ∧
    F*uniformRetainedTraceError D Y H h (periodizationSet Y H).card≤
      Real.exp (-Real.log (h+1:ℝ)/4) := by
  let s := Real.log (observationScale a (h+1))
  have hk : (1:ℝ)<h+1 := by exact_mod_cast (show 1<h+1 by omega)
  have hX : 0<observationScale a (h+1) := Real.exp_pos _
  have hexp : Real.exp s=observationScale a (h+1) := Real.exp_log hX
  have hshift := double_exp_mono (s:=s) (show K≤K+21 by linarith)
  have hcount := growing_periodization_card hY hH.le hK hs hHM hYM
  have htrace := growing_retained_trace_error hD hY hH hF (by linarith : 0≤K+21) hs
    (hDM.trans hshift) (hHM.trans hshift) (hYM.trans hshift) (hFM.trans hshift) h
    (periodizationSet Y H).card hcount
  have hcoef : geometryGrowthCoefficient+8+(K+21)=geometryGrowthCoefficient+29+K := by ring
  rw [hcoef,hexp] at htrace
  have hbridge := bridgeErrorThird_at_scale hk hL hscale
  constructor
  · have hbig := double_exp_mono (s:=s)
      (show K≤geometryGrowthCoefficient+29+K by linarith [geometryGrowthCoefficient_nonneg])
    have hm := mul_le_mul_of_nonneg_right (hDM.trans hbig)
      (by positivity : 0≤(h+1:ℝ)^(-(1/3:ℝ)))
    rw [double_exp_mul_trace_power,hexp] at hm
    have he : Real.exp (-Real.log (h+1:ℝ)/4)≤1 :=
      Real.exp_le_one_iff.mpr (by linarith [Real.log_pos hk])
    simpa only [mul_comm] using hm.trans (hbridge.trans he)
  · exact htrace.trans hbridge

#print axioms growing_retained_trace_at_scale

end QuantitativeHolomorphic.Schedule
