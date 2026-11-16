module

public import QuantitativeMaassCuspWaveDAlembertV1
public import QuantitativeMaassLogBandTranslationV1
public import QuantitativeMaassLogTestSeparationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff MatrixGroups InnerProductSpace

namespace QuantitativeMaass.Wave

/-- The genuine local free cosine evolution of the initial cusp constant
term: pull the two shifted bands back to the requested band and average. -/
def cuspLogFreeWave (N : ℕ) (hN : 0<N) (s : SL(2,ℤ)) (A B t : ℝ)
    (f : AutomorphicSpace N) : Lp ℂ 2 (volume.restrict (Icc A B)) :=
  (1/2:ℂ) •
    (logBandTranslate A B t (cuspLogConstant N hN s (t+A) (t+B) f)+
      logBandTranslate A B (-t) (cuspLogConstant N hN s (-t+A) (-t+B) f))

theorem cuspSmoothing_zero_space (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (f : AutomorphicSpace N) (t : ℝ) :
    cuspSmoothing N hN s A B ψ hψ f (t,0)=cuspLogWaveTest N hN s A B ψ hψ f t := by
  change localCuspSmoothing N hN s (0+A) (0+B) ψ hψ f (t,0)=_
  rw [zero_add,zero_add]
  unfold localCuspSmoothing cuspLogWaveTest translatedLogTest
  simp only [sub_zero]

theorem cuspSmoothing_zero_time (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (f : AutomorphicSpace N) (x : ℝ) :
    cuspSmoothing N hN s A B ψ hψ f (0,x)=
      inner ℂ (translatedLogTest (x+A) (x+B) ψ hψ x)
        (cuspLogConstant N hN s (x+A) (x+B) f) := by
  unfold cuspSmoothing localCuspSmoothing
  rw [shiftedQuotientWave_zero,ContinuousLinearMap.id_apply]

/-- Exact free-wave intertwining tested against every smooth supported
test, derived from the proved global smoothing formula. -/
theorem cuspLogWaveTest_free (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ⊆Icc A B) (f : AutomorphicSpace N) (t : ℝ) :
    cuspLogWaveTest N hN s A B ψ hψ.continuous f t=
      inner ℂ (logTestVector A B ψ hψ.continuous) (cuspLogFreeWave N hN s A B t f) := by
  have h := cuspSmoothing_dAlembert N hN s A B ψ hψ hs f t 0
  rw [cuspSmoothing_zero_space,zero_add,zero_sub,cuspSmoothing_zero_time,
    cuspSmoothing_zero_time] at h
  rw [h,cuspLogFreeWave,inner_smul_right,inner_add_right,
    logBandTranslate_pairing,logBandTranslate_pairing]
  ring

/-- ACTUAL all-cusp wave intertwining on local L2 classes. Every map is
constructed from the quotient wave, geometric averaging, half-density
coordinate change and literal translations. No weak-uniqueness or smoothing
regularity premise is present, and no full-line L2 assumption is made. -/
theorem cuspLogConstant_wave_eq_free (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (f : AutomorphicSpace N) (t : ℝ) :
    cuspLogConstant N hN s A B (shiftedQuotientWave N t f)=cuspLogFreeWave N hN s A B t f := by
  apply sub_eq_zero.mp
  apply logTestVector_separates A B
  intro ψ hψ hs
  rw [inner_sub_right]
  exact sub_eq_zero.mpr (cuspLogWaveTest_free N hN s A B ψ hψ hs f t)

#print axioms cuspLogWaveTest_free
#print axioms cuspLogConstant_wave_eq_free

end QuantitativeMaass.Wave
