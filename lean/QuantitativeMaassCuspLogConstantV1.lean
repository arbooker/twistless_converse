module

public import QuantitativeMaassHalfDensityTestV1
public import QuantitativeMaassCuspWaveAverageV1
public import QuantitativeMaassCuspAveragedWaveV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology ContDiff MatrixGroups InnerProductSpace

namespace QuantitativeMaass

/-- The actual all-cusp logarithmic half-density on a compact band. -/
def cuspLogConstant (N : ℕ) (hN : 0<N) (s : SL(2,ℤ)) (A B : ℝ) :
    AutomorphicSpace N →L[ℝ] Lp ℂ 2 (volume.restrict (Icc A B)) :=
  (localHalfDensity N A B (Nat.cast_pos.mpr hN)).comp
    ((cuspConstantLocal N s (Real.exp A) (Real.exp B) (Real.exp_pos A)).restrictScalars ℝ)

theorem cuspLogConstant_representative_ae (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) :
    (cuspLogConstant N hN s A B
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f) : ℝ → ℂ)
      =ᵐ[volume.restrict (Icc A B)] logHalfDensity (cuspConstant N s f.val) :=
  localHalfDensity_representative_ae N A B (Nat.cast_pos.mpr hN) _ _
    (cuspConstantLocal_representative_ae N hN s _ _ (Real.exp_pos A) f hf)

namespace Wave

theorem cuspLogConstant_wave_continuous (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (f : AutomorphicSpace N) :
    Continuous (fun t => cuspLogConstant N hN s A B (shiftedQuotientWave N t f)) :=
  (cuspLogConstant N hN s A B).continuous.comp (shiftedQuotientWave_stronglyContinuous N f)

/-- Logarithmic weak testing of the actual quotient wave. -/
def cuspLogWaveTest (N : ℕ) (hN : 0<N) (s : SL(2,ℤ)) (A B : ℝ)
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (f : AutomorphicSpace N) (t : ℝ) : ℂ :=
  inner ℂ (logTestVector A B ψ hψ)
    (cuspLogConstant N hN s A B (shiftedQuotientWave N t f))

theorem cuspWaveTest_log_pairing (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (g : ℝ → ℂ) (hg : Continuous g) (f : AutomorphicSpace N) (t : ℝ) :
    cuspWaveTest N s (Real.exp A) (Real.exp B) (Real.exp_pos A) g hg f t=
      (N:ℂ)*cuspLogWaveTest N hN s A B (logHalfDensity g)
        (logHalfDensity_continuous g hg) f t := by
  unfold cuspWaveTest cuspLogWaveTest cuspLogConstant
  rw [localHalfDensity_inner N A B (Nat.cast_pos.mpr hN),
    localHalfDensity_heightTest N A B (Nat.cast_pos.mpr hN)]
  rfl

/-- The conjugated Laplacian test is minus its ordinary second derivative
plus the one-quarter spectral shift, on the actual local L2 state. -/
theorem cuspWaveTest_log_laplacian (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (f : AutomorphicSpace N) (t : ℝ) :
    cuspWaveTest N s (Real.exp A) (Real.exp B) (Real.exp_pos A)
      (heightLaplacianTest g) (heightLaplacianTest_continuous g hg) f t=
      (N:ℂ)*(-cuspLogWaveTest N hN s A B (deriv (deriv (logHalfDensity g)))
        (logHalfDensity_second_continuous g hg) f t+
        (1/4:ℂ)*cuspLogWaveTest N hN s A B (logHalfDensity g)
          (logHalfDensity_continuous g hg.continuous) f t) := by
  unfold cuspWaveTest cuspLogWaveTest cuspLogConstant
  rw [localHalfDensity_inner N A B (Nat.cast_pos.mpr hN),
    localHalfDensity_laplacianTest N A B (Nat.cast_pos.mpr hN) g hg]
  simp only [inner_add_left,inner_neg_left,inner_smul_left,map_div₀,map_one,map_ofNat]
  rfl

#print axioms cuspLogConstant_representative_ae
#print axioms cuspLogConstant_wave_continuous
#print axioms cuspWaveTest_log_laplacian

end Wave
end QuantitativeMaass
