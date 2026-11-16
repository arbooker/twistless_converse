module

public import QuantitativeMaassCuspLogWeakEquationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff MatrixGroups InnerProductSpace

namespace QuantitativeMaass.Wave

theorem cuspLogWaveTest_continuous (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (f : AutomorphicSpace N) :
    Continuous (cuspLogWaveTest N hN s A B ψ hψ f) :=
  continuous_const.inner (cuspLogConstant_wave_continuous N hN s A B f)

/-- Each compact log-height test yields a genuine C2 time function.
This follows from the actual weak PDE and local L2 continuity. -/
theorem cuspLogWaveTest_contDiff_two (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B) (f : AutomorphicSpace N) :
    ContDiff ℝ 2 (cuspLogWaveTest N hN s A B ψ hψ.continuous f) := by
  have hsecond := cuspLogWaveTest_second_derivative N hN s A B ψ hψ hs f
  have he : deriv (deriv (cuspLogWaveTest N hN s A B ψ hψ.continuous f))=
      cuspLogWaveTest N hN s A B (deriv (deriv ψ))
        ((contDiff_infty_iff_deriv.mp hψ).2.continuous_deriv (by simp)) f :=
    funext (fun t => (hsecond t).deriv)
  rw [show (2:ℕ∞ω)=1+1 by rfl,contDiff_succ_iff_deriv]
  refine ⟨cuspLogWaveTest_differentiable N hN s A B ψ hψ hs f,by simp,?_⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hsecond t).differentiableAt,?_⟩
  rw [he]
  exact cuspLogWaveTest_continuous N hN s A B _ _ f

/-- The height test pairing is independent of the containing positive band:
its compact Poincare seed has the same underlying function in both cases. -/
theorem cuspWaveTest_band_independent (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (a b c d : ℝ) (ha : 0<a) (hc : 0<c)
    (hs : Function.support g⊆Icc a b) (hs' : Function.support g⊆Icc c d)
    (f : AutomorphicSpace N) (t : ℝ) :
    cuspWaveTest N s a b ha g hg.continuous f t=
      cuspWaveTest N s c d hc g hg.continuous f t := by
  unfold cuspWaveTest
  rw [← cuspPeriodTest_pairing N hN s g hg a b ha hs,
    ← cuspPeriodTest_pairing N hN s g hg c d hc hs']
  rfl

/-- Compatibility of logarithmic test pairings on overlapping compact bands.
Thus the constructed local states define a single weak cusp trajectory. -/
theorem cuspLogWaveTest_band_independent (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B C D : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B) (hs' : Function.support ψ⊆Icc C D)
    (f : AutomorphicSpace N) (t : ℝ) :
    cuspLogWaveTest N hN s A B ψ hψ.continuous f t=
      cuspLogWaveTest N hN s C D ψ hψ.continuous f t := by
  let g := inverseHalfDensityTest ψ
  have hg : ContDiff ℝ ∞ g := inverseHalfDensityTest_smooth ψ hψ A B hs
  have he := congrFun (cuspLogWaveTest_of_height N hN s A B g hg.continuous f) t
  have he' := congrFun (cuspLogWaveTest_of_height N hN s C D g hg.continuous f) t
  have hgψ : logHalfDensity g=ψ := logHalfDensity_inverse ψ
  simp only [hgψ] at he he'
  rw [he,he']
  congr 1
  exact cuspWaveTest_band_independent N hN s g hg _ _ _ _ (Real.exp_pos A) (Real.exp_pos C)
    (inverseHalfDensityTest_support ψ A B hs) (inverseHalfDensityTest_support ψ C D hs') f t

#print axioms cuspLogWaveTest_contDiff_two
#print axioms cuspLogWaveTest_band_independent

end QuantitativeMaass.Wave
