module

public import QuantitativeMaassEvenTimeCalculusV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A segment average retains a uniform norm bound. -/
theorem segmentAverage_norm_bound (k : ℕ) (f : ℝ → ℂ) (u M : ℝ) (hM : 0≤M)
    (hb : ∀ s∈Icc (0:ℝ) 1,‖f (s*u)‖≤M) : ‖segmentAverage k f u‖≤M := by
  have hh := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Icc (0:ℝ) 1)
    (f:=fun s => (s^k:ℝ) • f (s*u)) (by simp) (fun s hs => by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hs.1 _)]
      exact (mul_le_mul_of_nonneg_left (hb s hs) (pow_nonneg hs.1 _)).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hs.1 hs.2) hM))
  simpa only [segmentAverage,Real.volume_real_Icc_of_le (by norm_num : (0:ℝ)≤1),sub_zero,mul_one] using hh

/-- The elementary fundamental-theorem estimate with an exact zero value. -/
theorem smooth_zero_norm_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hz : f 0=0) (M : ℝ) (hM : 0≤M) (hb : ∀ u,‖deriv f u‖≤M) (u : ℝ) :
    ‖f u‖≤|u| *M := by
  have hi := segmentAverage_deriv_identity f hf u
  rw [hz,sub_zero] at hi
  rw [← hi,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (segmentAverage_norm_bound 0 (deriv f) u M hM (fun s _ => hb (s*u))) (abs_nonneg _)

/-- Evenness removes the constant term from the third derivative. -/
theorem even_third_derivative_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (M : ℝ) (hM : 0≤M)
    (hb : ∀ u,‖deriv (deriv (deriv (deriv f))) u‖≤M) (u : ℝ) :
    ‖deriv (deriv (deriv f)) u‖≤|u| *M := by
  have h1 := (contDiff_infty_iff_deriv.mp hf).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  have h3 := (contDiff_infty_iff_deriv.mp h2).2
  exact smooth_zero_norm_bound _ h3
    (even_time_deriv_zero _ (even_time_second_deriv_even f he)) M hM hb u

/-- Uniform control of the nonsingular f'(u)/u replacement and its derivative. -/
theorem evenRadialDerivative_bounds (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (M2 M4 : ℝ)
    (hM2 : 0≤M2) (hM4 : 0≤M4)
    (hb2 : ∀ u,‖deriv (deriv f) u‖≤M2)
    (hb4 : ∀ u,‖deriv (deriv (deriv (deriv f))) u‖≤M4) (u : ℝ) (hu : 0≤u) :
    ‖evenRadialDerivative f u‖≤M2 ∧ ‖deriv (evenRadialDerivative f) u‖≤u*M4 := by
  have h2 := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).2).2
  refine ⟨segmentAverage_norm_bound 0 _ u M2 hM2 (fun s _ => hb2 (s*u)),?_⟩
  rw [evenRadialDerivative,segmentAverage_deriv 0 _ h2 hc.deriv.deriv]
  apply segmentAverage_norm_bound 1 _ u (u*M4) (mul_nonneg hu hM4)
  intro s hs
  have hh := even_third_derivative_bound f hf he M4 hM4 hb4 (s*u)
  rw [abs_of_nonneg (mul_nonneg hs.1 hu)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by nlinarith [hs.2] : s*u≤u) hM4)

#print axioms segmentAverage_norm_bound
#print axioms smooth_zero_norm_bound
#print axioms even_third_derivative_bound
#print axioms evenRadialDerivative_bounds

end QuantitativeMaass
