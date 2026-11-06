module

public import QuantitativeArithmeticSmallLevelTwentyTwoCentersV1
public import SmallLevelAdditiveMellinV1
public import Mathlib.NumberTheory.LSeries.Linearity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane SmallLevelNormalized QuantitativeArithmeticTranslatedFricke
  FinitenessPolynomialSeries FinitenessFourierConstruction SmallLevelAdditive Complex MeasureTheory
open scoped MatrixGroups ModularForm

def tenthMellin (m : ℕ) (f : ℕ→ℂ) : ℂ→ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1100
    (tenthCoefficients (FinitenessOriginalFourier.fullCoefficients f (2*m))))

def evenTenthEntire (m : ℕ) (f : ℕ→ℂ) : ℂ→ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1
    (tenthCoefficients (FinitenessOriginalFourier.fullCoefficients f (2*m))))

/-- The even tenth sum has an entire finite-order Mellin transform and
its conductor-1100 functional equation, directly from original input. -/
theorem original_tenth_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧
      Differentiable ℂ (tenthMellin m f) ∧
      FinitenessFiniteOrder.Bound (tenthMellin m f) ∧
      ∀ s : ℂ, tenthMellin m f s=
        (χ/(Complex.I^(2*m)))*tenthMellin m f ((2*m:ℕ)-s) := by
  obtain ⟨χ,hχ,hn,hp⟩:=original_tenth_fricke m hf
  obtain ⟨τ,_,hg⟩:=hf.growth
  let a:=FinitenessOriginalFourier.fullCoefficients f (2*m)
  have ha : PolynomialBound a:=FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m)
  have ha0 : a 0=0:=FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)
  have hB0 : tenthCoefficients a 0=0 := by simp [tenthCoefficients,coefficients_zero ha0]
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ:=((2*m:ℕ):ℤ)
  have hfourier : (fun z : ℍ => fourier (tenthCoefficients a) z)=
      (F ∣[k] translation (1/10))+(F ∣[k] translation (-1/10)) := by
    funext z
    rw [tenth_fourier ha z z.im_pos]
    simp only [Pi.add_apply,translation_slash]
    change fourier a _+fourier a _=fourier a ((translation (1/10) • z:ℍ):ℂ)+
      fourier a ((translation (-1/10) • z:ℍ):ℂ)
    rw [translation_point,translation_point]
  have hslash : (fun z : ℍ => fourier (tenthCoefficients a) z) ∣[k] fricke 1100 (by decide)=
      χ • (fun z : ℍ => fourier (tenthCoefficients a) z) := by
    rw [hfourier,SlashAction.add_slash,hp,hn,← smul_add]
    congr 1
    abel
  have hl:=formula_of_slash 1100 (2*m) (by decide) (fourier (tenthCoefficients a)) χ hχ hslash
  have hχ0 : χ≠0 := by rcases hχ with rfl|rfl <;> norm_num
  refine ⟨χ,hχ,?_⟩
  apply FinitenessAllLevelMellinPair.mellin_entire (by decide : 0<1100) (by omega : 0<2*m)
    (tenthCoefficients a) (tenth_polynomial ha) hB0 (χ/(Complex.I^(2*m)))
    (div_ne_zero hχ0 (pow_ne_zero _ Complex.I_ne_zero))
  simpa only [div_mul_cancel₀ _ (pow_ne_zero (2*m) Complex.I_ne_zero)] using hl

/-- The entire unscaled even-tenth continuation agrees with the literal
sum of the two additive Dirichlet series in an initial half-plane. -/
theorem original_tenth_continuation (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) :
    Differentiable ℂ (evenTenthEntire m f) ∧
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → evenTenthEntire m f s=
      original (2*m) f (1/10) s+original (2*m) f (-1/10) s := by
  obtain ⟨χ,_,he,_,_⟩:=original_tenth_entire m hm hf
  refine ⟨QuantitativeArithmeticMellinScale.entire_at_one (by decide : 0<1100) _ he,?_⟩
  obtain ⟨τ,_,hg⟩:=hf.growth
  let a:=FinitenessOriginalFourier.fullCoefficients f (2*m)
  have ha : PolynomialBound a:=FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m)
  have ha0 : a 0=0:=FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)
  have hB0 : tenthCoefficients a 0=0 := by simp [tenthCoefficients,coefficients_zero ha0]
  obtain ⟨B,hB⟩:=common_halfplane (tenth_polynomial ha) hB0
  obtain ⟨d,hd⟩:=FinitenessAllLevelMellinDirichlet.polynomial_growth ha
  refine ⟨max B ((d:ℝ)+1),fun s hs => ?_⟩
  have hsB : B<s.re := (le_max_left _ _).trans_lt hs
  have hsd : (d:ℝ)+1<s.re := (le_max_right _ _).trans_lt hs
  have hh:=(hB 0 s hsB).2
  have hc0 : coefficients (tenthCoefficients a) 0=tenthCoefficients a := by
    funext n
    simp [coefficients,phase]
  have hL : LSeries (tenthCoefficients a) s=
      LSeries (coefficients a (1/10)) s+LSeries (coefficients a (-1/10)) s :=
    LSeries_add (summable_at hd _ hsd) (summable_at hd _ hsd)
  change evenTenthEntire m f s=transform a (1/10) s+transform a (-1/10) s
  have hmain : evenTenthEntire m f s=transform (tenthCoefficients a) 0 s := by
    have haxis : FinitenessAllLevelAxisDecay.axis 1 (tenthCoefficients a)=
        (fun t : ℝ => fourier (tenthCoefficients a) ((t:ℂ)*Complex.I)) := by
      funext t
      simp [FinitenessAllLevelAxisDecay.axis]
    change mellin (FinitenessAllLevelAxisDecay.axis 1 (tenthCoefficients a)) s=_
    rw [haxis]
    simpa only [Complex.ofReal_zero,zero_add] using hh
  rw [hmain,transform,hc0,hL,transform,transform]
  ring

#print axioms original_tenth_entire
#print axioms original_tenth_continuation
end QuantitativeArithmeticSmallLevelTwentyTwo
