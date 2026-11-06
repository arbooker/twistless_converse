module
public import SmallLevelEvenScaleV1
public import SmallLevelNormalizedMatricesV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelEvenScale
open Complex UpperHalfPlane SmallLevelNormalized
open FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

theorem original_half_translation {L : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.EulerData (4*L) f) (k : ℕ) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/2)=
      -SmallLevelOriginal.fourierFunction k f := by
  funext z
  rw [translation_slash]
  have hh:=scaled_antiperiod hf k (z:=2*(z:ℂ)) (by
    simpa [mul_im] using
      mul_pos (by norm_num : (0:ℝ)<2) z.im_pos)
  have h1 : (2*(z:ℂ)+1)/2=(z:ℂ)+1/2 := by ring
  have h2 : 2*(z:ℂ)/2=(z:ℂ) := by ring
  simpa only [scaledFourier,h1,h2,SmallLevelOriginal.fourierFunction,
    translation_point,ofReal_div,ofReal_one,ofReal_ofNat,Pi.neg_apply] using hh

#print axioms original_half_translation
end SmallLevelEvenScale
