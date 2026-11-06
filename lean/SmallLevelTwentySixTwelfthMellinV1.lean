module

public import SmallLevelTwentySixTwelfthCentersV1
public import SmallLevelAdditiveMellinV1
public import Mathlib.NumberTheory.LSeries.Linearity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixTwelfth
open SmallLevelTwentyEightTwelfth (twelfthCoefficients twelfth_polynomial twelfth_fourier)
open Matrix UpperHalfPlane SmallLevelNormalized QuantitativeArithmeticTranslatedFricke
  FinitenessPolynomialSeries FinitenessFourierConstruction SmallLevelAdditive Complex MeasureTheory
open scoped MatrixGroups ModularForm

def twelfthMellin (m : ℕ) (f : ℕ→ℂ) : ℂ→ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1872
    (twelfthCoefficients (FinitenessOriginalFourier.fullCoefficients f (2*m))))

def twelfthEntire (m : ℕ) (f : ℕ→ℂ) : ℂ→ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1
    (twelfthCoefficients (FinitenessOriginalFourier.fullCoefficients f (2*m))))

/-- The twelfth difference has an entire finite-order Mellin transform and
its conductor-1872 functional equation, directly from original input. -/
theorem original_twelfth_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f) :
      Differentiable ℂ (twelfthMellin m f) ∧
      FinitenessFiniteOrder.Bound (twelfthMellin m f) ∧
      ∀ s : ℂ, twelfthMellin m f s=
        ((-(FinitenessNormalizedTwistProduct.root 26 f 2*η))/(Complex.I^(2*m)))*twelfthMellin m f ((2*m:ℕ)-s) := by
  obtain ⟨hn,hp⟩:=original_twelfth_fricke m hf η hη hW
  have hχ : -(FinitenessNormalizedTwistProduct.root 26 f 2*η)=1 ∨ -(FinitenessNormalizedTwistProduct.root 26 f 2*η)= -1 := by
    rcases FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2 with h|h <;>
      rcases hη with h'|h' <;> simp [h,h']
  obtain ⟨τ,_,hg⟩:=hf.growth
  let a:=FinitenessOriginalFourier.fullCoefficients f (2*m)
  have ha : PolynomialBound a:=FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m)
  have ha0 : a 0=0:=FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)
  have hB0 : twelfthCoefficients a 0=0 := by simp [twelfthCoefficients,coefficients_zero ha0]
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ:=((2*m:ℕ):ℤ)
  have hfourier : (fun z : ℍ => fourier (twelfthCoefficients a) z)=
      (F ∣[k] translation (1/12))-(F ∣[k] translation (-1/12)) := by
    funext z
    rw [twelfth_fourier ha z z.im_pos]
    simp only [Pi.sub_apply,translation_slash]
    change fourier a _-fourier a _=fourier a ((translation (1/12) • z:ℍ):ℂ)-
      fourier a ((translation (-1/12) • z:ℍ):ℂ)
    rw [translation_point,translation_point]
  have hslash : (fun z : ℍ => fourier (twelfthCoefficients a) z) ∣[k] fricke 1872 (by decide)=
      (-(FinitenessNormalizedTwistProduct.root 26 f 2*η)) • (fun z : ℍ => fourier (twelfthCoefficients a) z) := by
    rw [hfourier,sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash,hp,hn]
    simp only [_root_.neg_smul,smul_add,smul_neg]
    abel
  have hl:=formula_of_slash 1872 (2*m) (by decide) (fourier (twelfthCoefficients a)) (-(FinitenessNormalizedTwistProduct.root 26 f 2*η)) hχ hslash
  have hχ0 : -(FinitenessNormalizedTwistProduct.root 26 f 2*η)≠0 := by
    rcases hχ with h|h <;> rw [h] <;> norm_num
  apply FinitenessAllLevelMellinPair.mellin_entire (by decide : 0<1872) (by omega : 0<2*m)
    (twelfthCoefficients a) (twelfth_polynomial ha) hB0 ((-(FinitenessNormalizedTwistProduct.root 26 f 2*η))/(Complex.I^(2*m)))
    (div_ne_zero hχ0 (pow_ne_zero _ Complex.I_ne_zero))
  simpa only [div_mul_cancel₀ _ (pow_ne_zero (2*m) Complex.I_ne_zero)] using hl

/-- The entire unscaled even-twelfth continuation agrees with the literal
difference of the two additive Dirichlet series in an initial half-plane. -/
theorem original_twelfth_continuation (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f) :
    Differentiable ℂ (twelfthEntire m f) ∧
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → twelfthEntire m f s=
      original (2*m) f (1/12) s-original (2*m) f (-1/12) s := by
  obtain ⟨he,_,_⟩:=original_twelfth_entire m hm hf η hη hW
  refine ⟨QuantitativeArithmeticMellinScale.entire_at_one (by decide : 0<1872) _ he,?_⟩
  obtain ⟨τ,_,hg⟩:=hf.growth
  let a:=FinitenessOriginalFourier.fullCoefficients f (2*m)
  have ha : PolynomialBound a:=FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m)
  have ha0 : a 0=0:=FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)
  have hB0 : twelfthCoefficients a 0=0 := by simp [twelfthCoefficients,coefficients_zero ha0]
  obtain ⟨B,hB⟩:=common_halfplane (twelfth_polynomial ha) hB0
  obtain ⟨d,hd⟩:=FinitenessAllLevelMellinDirichlet.polynomial_growth ha
  refine ⟨max B ((d:ℝ)+1),fun s hs => ?_⟩
  have hsB : B<s.re := (le_max_left _ _).trans_lt hs
  have hsd : (d:ℝ)+1<s.re := (le_max_right _ _).trans_lt hs
  have hh:=(hB 0 s hsB).2
  have hc0 : coefficients (twelfthCoefficients a) 0=twelfthCoefficients a := by
    funext n
    simp [coefficients,phase]
  have hL : LSeries (twelfthCoefficients a) s=
      LSeries (coefficients a (1/12)) s-LSeries (coefficients a (-1/12)) s :=
    LSeries_sub (summable_at hd _ hsd) (summable_at hd _ hsd)
  change twelfthEntire m f s=transform a (1/12) s-transform a (-1/12) s
  have hmain : twelfthEntire m f s=transform (twelfthCoefficients a) 0 s := by
    have haxis : FinitenessAllLevelAxisDecay.axis 1 (twelfthCoefficients a)=
        (fun t : ℝ => fourier (twelfthCoefficients a) ((t:ℂ)*Complex.I)) := by
      funext t
      simp [FinitenessAllLevelAxisDecay.axis]
    change mellin (FinitenessAllLevelAxisDecay.axis 1 (twelfthCoefficients a)) s=_
    rw [haxis]
    simpa only [Complex.ofReal_zero,zero_add] using hh
  rw [hmain,transform,hc0,hL,transform,transform]
  ring

#print axioms original_twelfth_entire
#print axioms original_twelfth_continuation
end SmallLevelTwentySixTwelfth
