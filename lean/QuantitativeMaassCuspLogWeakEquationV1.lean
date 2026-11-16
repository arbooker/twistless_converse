module

public import QuantitativeMaassCuspLogWaveV1
public import QuantitativeMaassInverseHalfDensityTestV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff MatrixGroups InnerProductSpace

namespace QuantitativeMaass.Wave

theorem cuspLogWaveTest_congr (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ χ : ℝ → ℂ) (hψ : Continuous ψ) (hχ : Continuous χ)
    (he : ψ=χ) (f : AutomorphicSpace N) :
    cuspLogWaveTest N hN s A B ψ hψ f=cuspLogWaveTest N hN s A B χ hχ f := by
  subst χ
  rfl

/-- Weak time differentiability for every smooth supported logarithmic test. -/
theorem cuspLogWaveTest_differentiable (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B) (f : AutomorphicSpace N) :
    Differentiable ℝ (cuspLogWaveTest N hN s A B ψ hψ.continuous f) := by
  have h := cuspLogWaveTest_height_differentiable N hN s A B (inverseHalfDensityTest ψ)
      (inverseHalfDensityTest_smooth ψ hψ A B hs)
      (inverseHalfDensityTest_support ψ A B hs) f
  rw [cuspLogWaveTest_congr N hN s A B _ ψ _ hψ.continuous (logHalfDensity_inverse ψ) f] at h
  exact h

/-- The actual local half-density of the quotient wave solves u_tt=u_xx
against EVERY smooth compactly supported log-height test. All maps and
coordinate changes are constructed from the quotient Hilbert space. -/
theorem cuspLogWaveTest_second_derivative (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B) (f : AutomorphicSpace N) (t : ℝ) :
    HasDerivAt (deriv (cuspLogWaveTest N hN s A B ψ hψ.continuous f))
      (cuspLogWaveTest N hN s A B (deriv (deriv ψ))
        ((contDiff_infty_iff_deriv.mp hψ).2.continuous_deriv (by simp)) f t) t := by
  have h := cuspLogWaveTest_height_second_derivative N hN s A B (inverseHalfDensityTest ψ)
      (inverseHalfDensityTest_smooth ψ hψ A B hs)
      (inverseHalfDensityTest_support ψ A B hs) f t
  rw [cuspLogWaveTest_congr N hN s A B _ ψ _ hψ.continuous (logHalfDensity_inverse ψ) f] at h
  have he := cuspLogWaveTest_congr N hN s A B _ (deriv (deriv ψ))
    (logHalfDensity_second_continuous (inverseHalfDensityTest ψ)
      (inverseHalfDensityTest_smooth ψ hψ A B hs))
    ((contDiff_infty_iff_deriv.mp hψ).2.continuous_deriv (by simp))
    (congrArg (fun g => deriv (deriv g)) (logHalfDensity_inverse ψ)) f
  rw [he] at h
  exact h

theorem cuspLogWaveTest_initial_velocity (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B) (f : AutomorphicSpace N) :
    deriv (cuspLogWaveTest N hN s A B ψ hψ.continuous f) 0=0 := by
  have h := cuspLogWaveTest_height_initial_velocity N hN s A B (inverseHalfDensityTest ψ)
      (inverseHalfDensityTest_smooth ψ hψ A B hs)
      (inverseHalfDensityTest_support ψ A B hs) f
  rw [cuspLogWaveTest_congr N hN s A B _ ψ _ hψ.continuous (logHalfDensity_inverse ψ) f] at h
  exact h

#print axioms cuspLogWaveTest_differentiable
#print axioms cuspLogWaveTest_second_derivative
#print axioms cuspLogWaveTest_initial_velocity

end QuantitativeMaass.Wave
