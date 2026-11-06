module

public import SmallLevelTwentyOneKnownWordsTheoryV4
public import SmallLevelTranslatedMellinPairV1
public import QuantitativeArithmeticMellinScaleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyOneTenthMellin
open Complex MeasureTheory FinitenessFourierConstruction SmallLevelAdditive
open FinitenessAllLevelAxisDecay

def center (positive : Bool) : ℝ := if positive then 1/10 else -(1/10)

def scaledCenter (m : ℕ) (f : ℕ → ℂ) (positive : Bool) : ℂ → ℂ :=
  mellin (axis 2100 (coefficients (FinitenessOriginalFourier.fullCoefficients f (2*m)) (center positive)))

def centerEntire (m : ℕ) (f : ℕ → ℂ) (positive : Bool) : ℂ → ℂ :=
  mellin (axis 1 (coefficients (FinitenessOriginalFourier.fullCoefficients f (2*m)) (center positive)))

theorem original_scaled_centers {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε) :
    ∀ b : Bool, Differentiable ℂ (scaledCenter m f b) ∧
      FinitenessFiniteOrder.Bound (scaledCenter m f b) ∧
      ∀ s : ℂ, scaledCenter m f b s=ε*scaledCenter m f (!b) (((2*m:ℕ):ℂ)-s) := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  obtain ⟨hχ,_⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<21) m ε hε hlaw
  have hh := SmallLevelTranslatedMellinPair.translated_pair_entire 2100 (2*m)
    (by decide) (by omega) (FinitenessOriginalFourier.fullCoefficients f (2*m))
    (FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m))
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m))
    (-1/10) (1/10) (ε*I^(2*m)) hχ
    (SmallLevelTwentyOneKnownWords.original_tenth_exchange hf ε hε hlaw)
  have he : (ε*I^(2*m))/I^(2*m)=ε := mul_div_cancel_right₀ ε (pow_ne_zero _ I_ne_zero)
  have hei : ε⁻¹=ε := by rcases hε with rfl|rfl <;> norm_num
  intro b
  cases b
  · simpa only [scaledCenter,center,Bool.false_eq_true,ite_false,ite_true,
      Bool.not_false,neg_div,he,hei] using hh.2
  · simpa only [scaledCenter,center,ite_true,Bool.false_eq_true,ite_false,
      Bool.not_true,neg_div,he] using hh.1

theorem original_center_continuations {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε) :
    (∀ b : Bool, Differentiable ℂ (centerEntire m f b)) ∧
    ∃ B : ℝ, ∀ b : Bool, ∀ s : ℂ, B<s.re →
      centerEntire m f b s=SmallLevelAdditive.original (2*m) f (center b) s := by
  have he := original_scaled_centers hm hf ε hε hlaw
  refine ⟨fun b => QuantitativeArithmeticMellinScale.entire_at_one (by decide : 0<2100)
    _ (he b).1,?_⟩
  obtain ⟨B,hB⟩ := SmallLevelAdditive.original_common_halfplane hf
  refine ⟨B,fun b s hs => ?_⟩
  have haxis : axis 1 (coefficients (FinitenessOriginalFourier.fullCoefficients f (2*m)) (center b))=
      (fun t : ℝ => fourier (FinitenessOriginalFourier.fullCoefficients f (2*m))
        ((center b:ℂ)+(t:ℂ)*I)) := funext (axis_one_translate _ _)
  unfold centerEntire
  rw [haxis]
  exact (hB (center b) s hs).2

#print axioms original_scaled_centers
#print axioms original_center_continuations
end SmallLevelTwentyOneTenthMellin
