module
public import QuantitativeArithmeticMaassClassicalWaveUniquenessV1
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff

namespace QuantitativeArithmeticMaassLocalWave

/-- Spatial smoothing written as translated test-function pairing. At x=0
it is the original test pairing, so no approximate-identity limit is needed. -/
def testAverage (u : ℝ → ℝ → ℂ) (g : ℝ → ℝ) (p : ℝ × ℝ) : ℂ :=
  ∫ y, g (y-p.2) • u p.1 y

/-- Reduction from locally integrable solutions to their classical smoothings.
The C2 regularity and classical PDE hypotheses must still be derived from the
weak equation before this yields weak-wave uniqueness. -/
theorem ae_zero_of_classical_testAverages (u : ℝ → ℝ → ℂ)
    (hu : ∀ t, LocallyIntegrable (u t))
    (hclassical : ∀ (g : ℝ → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      ContDiff ℝ 2 (testAverage u g) ∧
      (∀ p, fderiv ℝ (fderiv ℝ (testAverage u g)) p (1,0) (1,0)=
        fderiv ℝ (fderiv ℝ (testAverage u g)) p (0,1) (0,1)) ∧
      (∀ x, testAverage u g (0,x)=0) ∧
      (∀ x, fderiv ℝ (testAverage u g) (0,x) (1,0)=0))
    (t : ℝ) : ∀ᵐ x, u t x=0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero (hu t)
  intro g hg hs
  obtain ⟨hc,hp,hv,hd⟩ := hclassical g hg hs
  have h := classical_wave_zero (testAverage u g) hc hp hv hd t 0
  simpa only [testAverage,sub_zero] using h

#print axioms ae_zero_of_classical_testAverages
end QuantitativeArithmeticMaassLocalWave
