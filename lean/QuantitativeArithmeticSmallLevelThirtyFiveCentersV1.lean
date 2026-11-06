module

public import QuantitativeArithmeticTranslatedFrickeTheoryV4
public import SmallLevelSixRootsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveCenters
open SmallLevelNormalized SmallLevelThirtyFive SmallLevelOriginal
  QuantitativeArithmeticTranslatedFricke Complex Filter Set MeasureTheory
  FinitenessPolynomialSeries FinitenessFourierConstruction Matrix UpperHalfPlane
open scoped Topology MatrixGroups ModularForm

def center (positive : Bool) : ℝ := if positive then 1/6 else -(1/6)

/-- The original level35 input supplies both individual denominator-six
Fricke laws, with one common sign, via the proved modulus-six invariance. -/
theorem original_centers (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ positive : Bool,
      (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center positive))
        ∣[((2*m:ℕ):ℤ)] fricke 1260 (by decide)=
      χ • (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center positive)) := by
  obtain ⟨χ,hχ,hF⟩ := original_fricke_sign (by decide : 0<35) m hf
  refine ⟨χ,hχ,?_⟩
  intro positive
  cases positive
  · exact translated_slash 35 1260 (2*m) (by decide) (by decide) _ χ _ A A_det
      hF (SmallLevelSixEigen.thirty_five_A (by omega) hf) fricke_branch_neg
  · exact translated_slash 35 1260 (2*m) (by decide) (by decide) _ χ _ B B_det
      hF (SmallLevelSixEigen.thirty_five_B (by omega) hf) fricke_branch_pos

def centeredMellin (m : ℕ) (f : ℕ → ℂ) (positive : Bool) : ℂ → ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1260
    (SmallLevelAdditive.coefficients (FinitenessOriginalFourier.fullCoefficients f (2*m)) (center positive)))

/-- Actual entire finite-order continuations and functional equations for
both denominator-six additive twists, obtained from original input alone. -/
theorem original_centers_entire (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ positive : Bool,
      Differentiable ℂ (centeredMellin m f positive) ∧
      FinitenessFiniteOrder.Bound (centeredMellin m f positive) ∧
      ∀ s : ℂ, centeredMellin m f positive s=
        (χ/(Complex.I^(2*m)))*centeredMellin m f positive ((2*m:ℕ)-s) := by
  obtain ⟨χ,hχ,hF⟩ := original_centers m hm hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  refine ⟨χ,hχ,fun positive => ?_⟩
  exact translated_mellin_entire 1260 (2*m) (by decide) (by omega) _
    (FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m))
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)) (center positive) χ hχ
    (hF positive)

#print axioms original_centers
#print axioms original_centers_entire
end QuantitativeArithmeticSmallLevelThirtyFiveCenters
