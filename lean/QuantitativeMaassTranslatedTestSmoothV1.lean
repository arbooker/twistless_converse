module

public import QuantitativeMaassTranslatedTestRemainderV1
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Support

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

namespace QuantitativeMaass

/-- Spatial differentiation of translated tests in the actual local L2 norm. -/
theorem translatedLogTest_hasDerivAt_of_lipschitz (A B : ℝ) (g g' : ℝ → ℂ)
    (hg : Continuous g) (hg' : Continuous g') (K : ℝ≥0)
    (hd : ∀ x, HasDerivAt g (g' x) x) (hK : LipschitzWith K g') (x : ℝ) :
    HasDerivAt (translatedLogTest A B g hg) (-translatedLogTest A B g' hg' x) x := by
  apply HasDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  let M : ℝ := (measureUnivNNReal (volume.restrict (Icc A B)):ℝ)^((2:ENNReal).toReal⁻¹)*(K:ℝ)
  have hM : 0≤M := mul_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _) K.coe_nonneg
  have hpos : 0<M+1 := by linarith
  filter_upwards [Metric.ball_mem_nhds x (div_pos hε hpos)] with z hz
  have hz' : ‖z-x‖*(M+1)<ε := (lt_div_iff₀ hpos).mp (by simpa only [Metric.mem_ball,dist_eq_norm] using hz)
  have hsmall : M*‖z-x‖≤ε := by nlinarith [norm_nonneg (z-x)]
  calc
    _ ≤ M*‖z-x‖^2 := by
      simpa only [M,mul_assoc] using translatedLogTest_remainder_le A B g g' hg hg' K hd hK x z
    _ ≤ ε*‖z-x‖ := by nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg (z-x))]

theorem translatedLogTest_hasDerivAt (A B : ℝ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) (x : ℝ) :
    HasDerivAt (translatedLogTest A B g hg.continuous)
      (-translatedLogTest A B (deriv g) (hg.continuous_deriv (by simp)) x) x := by
  have hd := (contDiff_infty_iff_deriv.mp hg).2
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs.deriv hd (by simp)
  exact translatedLogTest_hasDerivAt_of_lipschitz A B g (deriv g) hg.continuous
    (hg.continuous_deriv (by simp)) K (fun y => (hg.differentiable (by simp) y).hasDerivAt) hK x

/-- Smooth compact scalar tests give smooth curves of translated local
L2 vectors. The derivative is proved in norm, not merely pointwise. -/
theorem translatedLogTest_contDiff_nat (n : ℕ) (A B : ℝ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) :
    ContDiff ℝ n (translatedLogTest A B g hg.continuous) := by
  induction n generalizing g with
  | zero =>
    rw [Nat.cast_zero,contDiff_zero]
    exact continuous_iff_continuousAt.mpr (fun x => (translatedLogTest_hasDerivAt A B g hg hs x).continuousAt)
  | succ n ih =>
    have hd := (contDiff_infty_iff_deriv.mp hg).2
    have he : deriv (translatedLogTest A B g hg.continuous)=
        fun x => -translatedLogTest A B (deriv g) hd.continuous x :=
      funext (fun x => (translatedLogTest_hasDerivAt A B g hg hs x).deriv)
    rw [Nat.cast_succ,contDiff_succ_iff_deriv]
    refine ⟨fun x => (translatedLogTest_hasDerivAt A B g hg hs x).differentiableAt,by simp,?_⟩
    rw [he]
    exact (ih (deriv g) hd hs.deriv).neg

theorem translatedLogTest_smooth (A B : ℝ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) :
    ContDiff ℝ ∞ (translatedLogTest A B g hg.continuous) :=
  contDiff_infty.mpr (fun n => translatedLogTest_contDiff_nat n A B g hg hs)

#print axioms translatedLogTest_hasDerivAt
#print axioms translatedLogTest_smooth

end QuantitativeMaass
