module

public import QuantitativeArithmeticTranslatedFrickeTheoryV4
public import SmallLevelTwoMellinReverseV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTranslatedMellinPair
open UpperHalfPlane SmallLevelNormalized SmallLevelAdditive Complex MeasureTheory
  FinitenessPolynomialSeries FinitenessFourierConstruction FinitenessAllLevelAxisDecay
open scoped ModularForm

theorem formula_of_exchange (N k : ℕ) (hN : 0<N) (F G : ℂ → ℂ) (χ : ℂ)
    (hχ : χ=1 ∨ χ= -1)
    (hF : (fun z : ℍ => F z) ∣[(k:ℤ)] fricke N hN=χ • (fun z : ℍ => G z)) :
    ∀ z : ℂ, 0<z.im → G z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z)) := by
  have hback : (fun z : ℍ => G z)=χ • ((fun z : ℍ => F z) ∣[(k:ℤ)] fricke N hN) := by
    rcases hχ with rfl|rfl
    · simpa using hF.symm
    · simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg hF.symm
  intro z hz
  have h := congrFun hback ⟨z,hz⟩
  rw [Pi.smul_apply,smul_eq_mul,det_one_slash _ (fricke_det _ _),fricke_denom,fricke_point] at h
  simpa only [zpow_neg,zpow_natCast,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h

/-- Exchanged Fourier translates give two actual entire Mellin transforms
and reflected equations, even when neither translate is individually fixed. -/
theorem translated_pair_entire (N k : ℕ) (hN : 0<N) (hk : 0<k)
    (a : ℕ → ℂ) (ha : PolynomialBound a) (ha0 : a 0=0)
    (r t : ℝ) (χ : ℂ) (hχ : χ=1 ∨ χ= -1)
    (hF : ((fun z : ℍ => fourier a z) ∣[(k:ℤ)] translation r) ∣[(k:ℤ)] fricke N hN=
      χ • ((fun z : ℍ => fourier a z) ∣[(k:ℤ)] translation t)) :
    (Differentiable ℂ (mellin (axis N (coefficients a t))) ∧
      FinitenessFiniteOrder.Bound (mellin (axis N (coefficients a t))) ∧
      ∀ s : ℂ, mellin (axis N (coefficients a t)) s=
        (χ/Complex.I^k)*mellin (axis N (coefficients a r)) ((k:ℂ)-s)) ∧
    (Differentiable ℂ (mellin (axis N (coefficients a r))) ∧
      FinitenessFiniteOrder.Bound (mellin (axis N (coefficients a r))) ∧
      ∀ s : ℂ, mellin (axis N (coefficients a r)) s=
        (χ/Complex.I^k)⁻¹*mellin (axis N (coefficients a t)) ((k:ℂ)-s)) := by
  have ht (u : ℝ) : (fun z : ℍ => fourier (coefficients a u) z)=
      (fun z : ℍ => fourier a z) ∣[(k:ℤ)] translation u := by
    funext z
    rw [translation_slash,translation_point,fourier_translate]
  have he := formula_of_exchange N k hN (fourier (coefficients a r))
    (fourier (coefficients a t)) χ hχ (by simpa only [ht] using hF)
  have hχ0 : χ≠0 := by rcases hχ with rfl|rfl <;> norm_num
  have hep : χ/Complex.I^k≠0 := div_ne_zero hχ0 (pow_ne_zero _ I_ne_zero)
  have hfr : ∀ z : ℂ, 0<z.im → fourier (coefficients a t) z=
      ((χ/Complex.I^k)*Complex.I^k)/(((Real.sqrt N:ℂ)*z)^k)*
        fourier (coefficients a r) (-1/((N:ℂ)*z)) := by
    simpa only [div_mul_cancel₀ _ (pow_ne_zero k I_ne_zero)] using he
  exact ⟨QuantitativeArithmeticSmallLevelNineteenTwoMellin.two_mellin_entire hN hk
    (coefficients a t) (coefficients a r) (coefficients_polynomial ha t) (coefficients_zero ha0 t)
    (coefficients_polynomial ha r) (coefficients_zero ha0 r) (χ/Complex.I^k) hep hfr,
    SmallLevelTwoMellin.two_mellin_reverse hN hk
    (coefficients a t) (coefficients a r) (coefficients_polynomial ha t) (coefficients_zero ha0 t)
    (coefficients_polynomial ha r) (coefficients_zero ha0 r) (χ/Complex.I^k) hep hfr⟩

#print axioms formula_of_exchange
#print axioms translated_pair_entire
end SmallLevelTranslatedMellinPair
