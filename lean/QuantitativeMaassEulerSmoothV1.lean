module

public import QuantitativeMaassEulerSeriesGradientV1
public import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Joint smoothness of every weighted moment series, proved by induction using
its actual Frechet derivative and the same family with increased indices. -/
theorem principalWeightedSeries_contDiffOn {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (j k σ : ℕ) :
    ContDiffOn ℝ ∞ (principalWeightedSeries b r j k σ) {z : ℝ × ℝ | 0<z.2} := by
  have hU : IsOpen {z : ℝ × ℝ | 0<z.2} := isOpen_lt continuous_const continuous_snd
  have h : ∀ m : ℕ,∀ j k σ,ContDiffOn ℝ m (principalWeightedSeries b r j k σ)
      {z : ℝ × ℝ | 0<z.2} := by
    intro m
    induction m with
    | zero =>
      intro j k σ
      exact contDiffOn_zero.mpr (principalWeightedSeries_continuousOn hb r j k σ)
    | succ m ih =>
      intro j k σ
      rw [Nat.cast_add,Nat.cast_one]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
      refine ⟨by simp,fun z => eulerGradient
        (((2*Real.pi:ℝ):ℂ)*Complex.I*principalWeightedSeries b r j (k+1) (σ+1) z)
        (-((2*Real.pi:ℝ):ℂ)*principalWeightedSeries b r (j+1) (k+1) σ z),?_,?_⟩
      · let A := ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ (ContinuousLinearMap.fst ℝ ℝ ℝ)
        let B := ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ (ContinuousLinearMap.snd ℝ ℝ ℝ)
        exact (A.contDiff.comp_contDiffOn (contDiffOn_const.mul (ih j (k+1) (σ+1)))).add
          (B.contDiff.comp_contDiffOn (contDiffOn_const.mul (ih (j+1) (k+1) σ)))
      · intro z hz
        exact (principalWeightedSeries_hasFDerivAt hb r j k σ z hz).hasFDerivWithinAt
  exact contDiffOn_infty.mpr (fun m => h m j k σ)

theorem principalEulerCore_contDiffOn {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) :
    ContDiffOn ℝ ∞ (principalEulerCore b r σ) {z : ℝ × ℝ | 0<z.2} := by
  rw [←principalWeightedSeries_zero]
  exact principalWeightedSeries_contDiffOn hb r 0 0 σ

/-- The literal original-coefficient Maass reconstruction is jointly smooth on
the upper half-plane. -/
theorem principalEulerWave_contDiffOn {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) :
    ContDiffOn ℝ ∞ (principalEulerWave b r σ) {z : ℝ × ℝ | 0<z.2} := by
  have hs : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Real.sqrt z.2) {z | 0<z.2} :=
    contDiff_snd.contDiffOn.sqrt (fun _ hz => ne_of_gt hz)
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hs).mul
    (principalEulerCore_contDiffOn hb r σ)

#print axioms principalWeightedSeries_contDiffOn
#print axioms principalEulerCore_contDiffOn
#print axioms principalEulerWave_contDiffOn

end QuantitativeMaass
