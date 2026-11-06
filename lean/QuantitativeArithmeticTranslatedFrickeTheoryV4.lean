module

public import FinitenessAllLevelMellinPairV1
public import SmallLevelAdditiveCoefficientsV1
public import SmallLevelNormalizedEvenFrickeV1

/-! Consolidated chapter: QuantitativeArithmeticTranslatedFricke. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticTranslatedFrickeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTranslatedFricke
open SmallLevelNormalized SmallLevelAdditive Complex Filter Set MeasureTheory
  FinitenessPolynomialSeries FinitenessFourierConstruction Matrix UpperHalfPlane
open scoped Topology MatrixGroups ModularForm

/-- A known matrix linking two Fricke centers gives an individual translated
Fricke law. No twisted functional equation is assumed. -/
theorem translated_slash (N L k : ℕ) (hN : 0<N) (hL : 0<L)
    (F : ℍ → ℂ) (χ : ℂ) (r : ℝ) (g : GL (Fin 2) ℝ)
    (hg : (GeneralLinearGroup.det g:ℝ)=1)
    (hF : F ∣[(k:ℤ)] fricke N hN=χ • F)
    (hG : F ∣[(k:ℤ)] g=F)
    (hbranch : fricke N hN*g*translation r=translation r*fricke L hL) :
    (F ∣[(k:ℤ)] translation r) ∣[(k:ℤ)] fricke L hL=
      χ • (F ∣[(k:ℤ)] translation r) := by
  rw [← SlashAction.slash_mul,← hbranch]
  simp only [SlashAction.slash_mul,hF,det_one_smul _ hg,hG,
    det_one_smul _ (translation_det _)]

theorem formula_of_slash (N k : ℕ) (hN : 0<N) (F : ℂ → ℂ) (χ : ℂ)
    (hχ : χ=1 ∨ χ= -1)
    (hF : (fun z : ℍ => F z) ∣[(k:ℤ)] fricke N hN=χ • (fun z : ℍ => F z)) :
    ∀ z : ℂ, 0<z.im → F z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z)) := by
  have hback : (fun z : ℍ => F z)=χ • ((fun z : ℍ => F z) ∣[(k:ℤ)] fricke N hN) := by
    rcases hχ with rfl|rfl
    · simpa using hF.symm
    · simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg hF.symm
  intro z hz
  have h := congrFun hback ⟨z,hz⟩
  rw [Pi.smul_apply,smul_eq_mul,det_one_slash _ (fricke_det _ _),fricke_denom,fricke_point] at h
  simpa only [zpow_neg,zpow_natCast,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h

/-- The Mellin transform of a Fourier translate is entire and of finite
order whenever its individual Fricke law has been derived. -/
theorem translated_mellin_entire (N k : ℕ) (hN : 0<N) (hk : 0<k)
    (a : ℕ → ℂ) (ha : PolynomialBound a) (ha0 : a 0=0)
    (r : ℝ) (χ : ℂ) (hχ : χ=1 ∨ χ= -1)
    (hF : ((fun z : ℍ => fourier a z) ∣[(k:ℤ)] translation r) ∣[(k:ℤ)] fricke N hN=
      χ • ((fun z : ℍ => fourier a z) ∣[(k:ℤ)] translation r)) :
    Differentiable ℂ (mellin (FinitenessAllLevelAxisDecay.axis N (coefficients a r))) ∧
    FinitenessFiniteOrder.Bound (mellin (FinitenessAllLevelAxisDecay.axis N (coefficients a r))) ∧
    ∀ s : ℂ, mellin (FinitenessAllLevelAxisDecay.axis N (coefficients a r)) s=
      (χ/(Complex.I^k))*mellin (FinitenessAllLevelAxisDecay.axis N (coefficients a r)) ((k:ℂ)-s) := by
  have ht : (fun z : ℍ => fourier (coefficients a r) z)=
      (fun z : ℍ => fourier a z) ∣[(k:ℤ)] translation r := by
    funext z
    rw [translation_slash,translation_point,fourier_translate]
  have hl := formula_of_slash N k hN (fourier (coefficients a r)) χ hχ (by simpa only [ht] using hF)
  have hχ0 : χ≠0 := by rcases hχ with rfl|rfl <;> norm_num
  apply FinitenessAllLevelMellinPair.mellin_entire hN hk (coefficients a r)
    (coefficients_polynomial ha r) (coefficients_zero ha0 r) (χ/(Complex.I^k))
    (div_ne_zero hχ0 (pow_ne_zero _ Complex.I_ne_zero))
  simpa only [div_mul_cancel₀ _ (pow_ne_zero k Complex.I_ne_zero)] using hl

#print axioms translated_slash
#print axioms formula_of_slash
#print axioms translated_mellin_entire
end QuantitativeArithmeticTranslatedFricke
end
end

/-! ## QuantitativeArithmeticTranslatedFrickeEigenV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticTranslatedFricke
open SmallLevelNormalized Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- The translated Fricke construction also carries an auxiliary matrix
character, rather than requiring that matrix to fix the function. -/
theorem translated_slash_eigen (N L k : ℕ) (hN : 0<N) (hL : 0<L)
    (F : ℍ→ℂ) (χ δ : ℂ) (r : ℝ) (g : GL (Fin 2) ℝ)
    (hg : (GeneralLinearGroup.det g:ℝ)=1)
    (hF : F ∣[(k:ℤ)] fricke N hN=χ • F)
    (hG : F ∣[(k:ℤ)] g=δ • F)
    (hbranch : fricke N hN*g*translation r=translation r*fricke L hL) :
    (F ∣[(k:ℤ)] translation r) ∣[(k:ℤ)] fricke L hL=
      (χ*δ) • (F ∣[(k:ℤ)] translation r) := by
  rw [← SlashAction.slash_mul,← hbranch]
  simp only [SlashAction.slash_mul,hF,det_one_smul _ hg,hG,
    det_one_smul _ (translation_det _),smul_smul]

#print axioms translated_slash_eigen
end QuantitativeArithmeticTranslatedFricke
end
end
