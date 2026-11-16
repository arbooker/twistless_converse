module

public import QuantitativeMaassCuspLogTestRegularityV1
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff MatrixGroups InnerProductSpace

namespace QuantitativeMaass.Wave

/-- Exact time derivative expressed using only the continuous local L2
trajectory and a second spatial derivative of the test. -/
theorem cuspLogWaveTest_deriv_integral (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B) (f : AutomorphicSpace N) (t : ℝ) :
    deriv (cuspLogWaveTest N hN s A B ψ hψ.continuous f) t=
      ∫ r in (0:ℝ)..t, cuspLogWaveTest N hN s A B (deriv (deriv ψ))
        ((contDiff_infty_iff_deriv.mp hψ).2.continuous_deriv (by simp)) f r := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := t)
    (fun r _ => cuspLogWaveTest_second_derivative N hN s A B ψ hψ hs f r)
    ((cuspLogWaveTest_continuous N hN s A B (deriv (deriv ψ))
      ((contDiff_infty_iff_deriv.mp hψ).2.continuous_deriv (by simp)) f).intervalIntegrable 0 t)
  rw [cuspLogWaveTest_initial_velocity N hN s A B ψ hψ hs f,sub_zero] at h
  exact h.symm

/-- The integrated weak equation. It avoids differentiating any L2
representative and is valid for both positive and negative times. -/
theorem cuspLogWaveTest_integrated (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B) (f : AutomorphicSpace N) (t : ℝ) :
    cuspLogWaveTest N hN s A B ψ hψ.continuous f t=
      cuspLogWaveTest N hN s A B ψ hψ.continuous f 0+
        ∫ r in (0:ℝ)..t, ∫ v in (0:ℝ)..r,
          cuspLogWaveTest N hN s A B (deriv (deriv ψ))
            ((contDiff_infty_iff_deriv.mp hψ).2.continuous_deriv (by simp)) f v := by
  have hd := cuspLogWaveTest_differentiable N hN s A B ψ hψ hs f
  have hc := (cuspLogWaveTest_contDiff_two N hN s A B ψ hψ hs f).continuous_deriv (by norm_num)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := t) (fun r _ => (hd r).hasDerivAt) (hc.intervalIntegrable 0 t)
  have he : deriv (cuspLogWaveTest N hN s A B ψ hψ.continuous f)=
      fun r => ∫ v in (0:ℝ)..r, cuspLogWaveTest N hN s A B (deriv (deriv ψ))
        ((contDiff_infty_iff_deriv.mp hψ).2.continuous_deriv (by simp)) f v :=
    funext (cuspLogWaveTest_deriv_integral N hN s A B ψ hψ hs f)
  rw [he] at hi
  linear_combination -hi

#print axioms cuspLogWaveTest_deriv_integral
#print axioms cuspLogWaveTest_integrated

end QuantitativeMaass.Wave
