module

public import QuantitativeMaassCuspLogConstantV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff MatrixGroups InnerProductSpace

namespace QuantitativeMaass.Wave

theorem cuspLogWaveTest_of_height (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (g : ℝ → ℂ) (hg : Continuous g) (f : AutomorphicSpace N) :
    cuspLogWaveTest N hN s A B (logHalfDensity g) (logHalfDensity_continuous g hg) f=
      fun t => (N:ℂ)⁻¹*cuspWaveTest N s (Real.exp A) (Real.exp B)
        (Real.exp_pos A) g hg f t := by
  funext t
  rw [cuspWaveTest_log_pairing N hN s A B g hg f t]
  have hn : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]

/-- First weak differentiability in logarithmic coordinates. -/
theorem cuspLogWaveTest_height_differentiable (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hs : Function.support g⊆Icc (Real.exp A) (Real.exp B)) (f : AutomorphicSpace N) :
    Differentiable ℝ
      (cuspLogWaveTest N hN s A B (logHalfDensity g) (logHalfDensity_continuous g hg.continuous) f) := by
  rw [cuspLogWaveTest_of_height N hN s A B g hg.continuous f]
  exact (cuspWaveTest_differentiable N hN s g hg _ _ (Real.exp_pos A) hs f).const_mul _

/-- The actual all-cusp wave satisfies the free weak wave equation for
all logarithmic images of smooth compactly supported positive-height tests. -/
theorem cuspLogWaveTest_height_second_derivative (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hs : Function.support g⊆Icc (Real.exp A) (Real.exp B)) (f : AutomorphicSpace N) (t : ℝ) :
    HasDerivAt (deriv (cuspLogWaveTest N hN s A B (logHalfDensity g)
      (logHalfDensity_continuous g hg.continuous) f))
      (cuspLogWaveTest N hN s A B (deriv (deriv (logHalfDensity g)))
        (logHalfDensity_second_continuous g hg) f t) t := by
  rw [cuspLogWaveTest_of_height N hN s A B g hg.continuous f,deriv_const_mul_field']
  have h := (cuspWaveTest_second_derivative N hN s g hg _ _ (Real.exp_pos A) hs f t).const_mul (N:ℂ)⁻¹
  apply h.congr_deriv
  rw [cuspWaveTest_log_pairing N hN s A B g hg.continuous f t,
    cuspWaveTest_log_laplacian N hN s A B g hg f t]
  have hn : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  field_simp
  ring

theorem cuspLogWaveTest_height_initial_velocity (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hs : Function.support g⊆Icc (Real.exp A) (Real.exp B)) (f : AutomorphicSpace N) :
    deriv (cuspLogWaveTest N hN s A B (logHalfDensity g)
      (logHalfDensity_continuous g hg.continuous) f) 0=0 := by
  rw [cuspLogWaveTest_of_height N hN s A B g hg.continuous f,deriv_const_mul_field,
    cuspWaveTest_initial_velocity N hN s g hg _ _ (Real.exp_pos A) hs f,mul_zero]

#print axioms cuspLogWaveTest_height_differentiable
#print axioms cuspLogWaveTest_height_second_derivative
#print axioms cuspLogWaveTest_height_initial_velocity

end QuantitativeMaass.Wave
