module

public import QuantitativeArithmeticTwoSequenceEntireTheoryV4
public import SmallLevelAdditiveMellinV1

/-! Consolidated chapter: QuantitativeArithmeticMatrixInfinityMellin. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticMatrixInfinityConvergentV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticMatrixInfinityMellin
open Complex Set MeasureTheory SmallLevelAdditive
open FinitenessPolynomialSeries FinitenessFourierConstruction

/-- A known matrix transformation makes the additive Mellin integral entire
at the real source that the matrix sends to infinity. -/
theorem matrix_source_convergent {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (k : ℕ) (hk : 0<k) (A B C D r : ℝ) (hC : C≠0)
    (hdet : 0<A*D-B*C) (hr : C*r+D=0) (χ : ℂ) (hχ : χ≠0)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((C:ℂ)*z+(D:ℂ))^k)*fourier a (((A:ℂ)*z+(B:ℂ))/((C:ℂ)*z+(D:ℂ)))) :
    ∀ s : ℂ, MellinConvergent (fun t : ℝ => fourier a ((r:ℂ)+(t:ℂ)*I)) s := by
  intro s
  have hL : 0<C^2/(A*D-B*C) := div_pos (sq_pos_of_ne_zero hC) hdet
  have hc : (C:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hC
  have hs : (Real.sqrt (C^2/(A*D-B*C)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL).ne'
  have hfr : ∀ z : ℂ, 0<z.im → fourier (coefficients a (-D/C)) z=
      (χ/(C:ℂ)^k)/z^k*
        fourier (coefficients a (A/C)) (-1/(((C^2/(A*D-B*C):ℝ):ℂ)*z)) := by
    intro z hz
    have hh := QuantitativeArithmeticTwoSequenceTaylor.matrix_two_series
      a k A B C D hC hdet χ hF z hz
    have hz0 : z≠0 := by intro he; subst z; simp at hz
    have hscalar : (χ*((Real.sqrt (C^2/(A*D-B*C)):ℂ)/(C:ℂ))^k)/
        (((Real.sqrt (C^2/(A*D-B*C)):ℂ)*z)^k)=(χ/(C:ℂ)^k)/z^k := by
      generalize (Real.sqrt (C^2/(A*D-B*C)):ℂ)=v at hs ⊢
      rw [div_pow,mul_pow]
      field_simp [hc,hs,hz0]
    simpa only [hscalar] using hh
  have hm := QuantitativeArithmeticTwoSequenceEntire.mellin_convergent
    (coefficients_polynomial ha (-D/C)) (coefficients_zero ha0 (-D/C))
    (coefficients_polynomial ha (A/C)) (coefficients_zero ha0 (A/C)) hL k hk
    (χ/(C:ℂ)^k) (div_ne_zero hχ (pow_ne_zero _ hc)) hfr s
  have hr' : -D/C=r := by
    apply (div_eq_iff hC).mpr
    nlinarith [hr]
  have he : (fun t : ℝ => fourier (coefficients a (-D/C)) ((t:ℂ)*I))=
      (fun t : ℝ => fourier a ((r:ℂ)+(t:ℂ)*I)) := by
    funext t
    rw [fourier_translate,hr',add_comm]
  rwa [he] at hm

#print axioms matrix_source_convergent
end QuantitativeArithmeticMatrixInfinityMellin
end
end

/-! ## QuantitativeArithmeticMatrixInfinityMellinV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticMatrixInfinityMellin
open Complex Set MeasureTheory SmallLevelAdditive
open FinitenessPolynomialSeries FinitenessFourierConstruction

/-- A known matrix transformation makes the additive Mellin integral entire
at the real source that the matrix sends to infinity. -/
theorem matrix_source_entire {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (k : ℕ) (hk : 0<k) (A B C D r : ℝ) (hC : C≠0)
    (hdet : 0<A*D-B*C) (hr : C*r+D=0) (χ : ℂ) (hχ : χ≠0)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((C:ℂ)*z+(D:ℂ))^k)*fourier a (((A:ℂ)*z+(B:ℂ))/((C:ℂ)*z+(D:ℂ)))) :
    Differentiable ℂ (mellin (fun t : ℝ => fourier a ((r:ℂ)+(t:ℂ)*I))) := by
  have hL : 0<C^2/(A*D-B*C) := div_pos (sq_pos_of_ne_zero hC) hdet
  have hc : (C:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hC
  have hs : (Real.sqrt (C^2/(A*D-B*C)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL).ne'
  have hfr : ∀ z : ℂ, 0<z.im → fourier (coefficients a (-D/C)) z=
      (χ/(C:ℂ)^k)/z^k*
        fourier (coefficients a (A/C)) (-1/(((C^2/(A*D-B*C):ℝ):ℂ)*z)) := by
    intro z hz
    have hh := QuantitativeArithmeticTwoSequenceTaylor.matrix_two_series
      a k A B C D hC hdet χ hF z hz
    have hz0 : z≠0 := by intro he; subst z; simp at hz
    have hscalar : (χ*((Real.sqrt (C^2/(A*D-B*C)):ℂ)/(C:ℂ))^k)/
        (((Real.sqrt (C^2/(A*D-B*C)):ℂ)*z)^k)=(χ/(C:ℂ)^k)/z^k := by
      generalize (Real.sqrt (C^2/(A*D-B*C)):ℂ)=v at hs ⊢
      rw [div_pow,mul_pow]
      field_simp [hc,hs,hz0]
    simpa only [hscalar] using hh
  have hm := QuantitativeArithmeticTwoSequenceEntire.mellin_entire
    (coefficients_polynomial ha (-D/C)) (coefficients_zero ha0 (-D/C))
    (coefficients_polynomial ha (A/C)) (coefficients_zero ha0 (A/C)) hL k hk
    (χ/(C:ℂ)^k) (div_ne_zero hχ (pow_ne_zero _ hc)) hfr
  have hr' : -D/C=r := by
    apply (div_eq_iff hC).mpr
    nlinarith [hr]
  have he : (fun t : ℝ => fourier (coefficients a (-D/C)) ((t:ℂ)*I))=
      (fun t : ℝ => fourier a ((r:ℂ)+(t:ℂ)*I)) := by
    funext t
    rw [fourier_translate,hr',add_comm]
  rwa [he] at hm

#print axioms matrix_source_entire
end QuantitativeArithmeticMatrixInfinityMellin
end
end
