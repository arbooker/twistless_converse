module

public import Mathlib.NumberTheory.LSeries.Linearity
public import SmallLevelAdditiveMellinV1
public import SmallLevelTwentySixTheoryV4
public import SmallLevelTwentySixTwelfthCentersV1

/-! Consolidated chapter: SmallLevelTwentySixQuarter. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixQuarterCentersV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixQuarter
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelTwentySix
open QuantitativeArithmeticTranslatedFricke FinitenessPolynomialSeries FinitenessFourierConstruction
  SmallLevelAdditive Complex MeasureTheory
open scoped MatrixGroups ModularForm

/-- The P law exchanges the quarter centers. Both signs are retained. -/
theorem quarter_fricke_of_P (m : ℕ) (F : ℍ→ℂ) (δ η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hW : F ∣[((2*m:ℕ):ℤ)] fricke 26 (by decide)=η • F)
    (hP : F ∣[((2*m:ℕ):ℤ)] P=δ • F) :
    ((F ∣[((2*m:ℕ):ℤ)] translation (-1/4)) ∣[((2*m:ℕ):ℤ)] fricke 208 (by decide)=
      (δ*η) • (F ∣[((2*m:ℕ):ℤ)] translation (1/4))) ∧
    ((F ∣[((2*m:ℕ):ℤ)] translation (1/4)) ∣[((2*m:ℕ):ℤ)] fricke 208 (by decide)=
      (δ*η) • (F ∣[((2*m:ℕ):ℤ)] translation (-1/4))) := by
  let k : ℤ:=((2*m:ℕ):ℤ)
  have hh:=congrArg (fun A : GL (Fin 2) ℝ => F ∣[k] A) P_factor4
  rw [SlashAction.slash_mul,SlashAction.slash_mul,hW,det_one_smul _ P_det,hP,
    det_one_smul _ (translation_det _),det_one_smul _ (translation_det _),
    smul_smul,SlashAction.slash_mul] at hh
  have hn : (F ∣[k] translation (-1/4)) ∣[k] fricke 208 (by decide)=
      (δ*η) • (F ∣[k] translation (1/4)) := by
    simpa only [neg_neg,mul_comm,neg_div] using hh.symm
  have hp:=congrArg (fun G : ℍ→ℂ => G ∣[k] fricke 208 (by decide)) hn
  rw [det_one_smul _ (fricke_det _ _)] at hp
  have hsquare : fricke 208 (by decide)*fricke 208 (by decide)=(-1:GL (Fin 2) ℝ) := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two]
    field_simp
  have he : ((F ∣[k] translation (-1/4)) ∣[k] fricke 208 (by decide))
      ∣[k] fricke 208 (by decide)=F ∣[k] translation (-1/4) := by
    rw [← SlashAction.slash_mul,hsquare]
    exact central_even _ m
  rw [he] at hp
  refine ⟨hn,?_⟩
  rcases hδ with h|h <;> rcases hη with h'|h' <;>
    simp only [h,h',mul_one,mul_neg,neg_neg,one_smul,neg_one_smul] at hp ⊢
  · exact hp.symm
  · simpa only [neg_neg] using congrArg Neg.neg hp.symm
  · simpa only [neg_neg] using congrArg Neg.neg hp.symm
  · exact hp.symm

def quarterCoefficients (a : ℕ→ℂ) (n : ℕ) : ℂ :=
  coefficients a (1/4) n-coefficients a (-1/4) n

theorem quarter_polynomial {a : ℕ→ℂ} (ha : PolynomialBound a) : PolynomialBound (quarterCoefficients a) := by
  obtain ⟨C,hC,d,hd⟩:=ha
  refine ⟨2*C,by positivity,d,fun n => ?_⟩
  calc
    ‖quarterCoefficients a n‖ ≤ ‖coefficients a (1/4) n‖+‖coefficients a (-1/4) n‖ := norm_sub_le _ _
    _ ≤ C*(1+(n:ℝ)^d)+C*(1+(n:ℝ)^d) := by simpa only [coefficients_norm] using add_le_add (hd n) (hd n)
    _ = 2*C*(1+(n:ℝ)^d) := by ring

theorem quarter_fourier {a : ℕ→ℂ} (ha : PolynomialBound a) (z : ℂ) (hz : 0<z.im) :
    fourier (quarterCoefficients a) z=fourier a (z+(1/4:ℝ))-fourier a (z+(-1/4:ℝ)) := by
  rw [← fourier_translate,← fourier_translate]
  simp only [fourier,sum_eq_tsum]
  simp only [quarterCoefficients,sub_mul]
  exact (summable (coefficients_polynomial ha _) (Function.Periodic.norm_qParam_lt_one (by norm_num) hz)).tsum_sub
    (summable (coefficients_polynomial ha _) (Function.Periodic.norm_qParam_lt_one (by norm_num) hz))


#print axioms quarter_fricke_of_P
#print axioms quarter_fourier
end SmallLevelTwentySixQuarter
end
end

/-! ## SmallLevelTwentySixQuarterMellinV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixQuarter
open SmallLevelTwentySix (P)
open Matrix UpperHalfPlane SmallLevelNormalized QuantitativeArithmeticTranslatedFricke
  FinitenessPolynomialSeries FinitenessFourierConstruction SmallLevelAdditive Complex MeasureTheory
open scoped MatrixGroups ModularForm

def quarterMellin (m : ℕ) (f : ℕ→ℂ) : ℂ→ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 208
    (quarterCoefficients (FinitenessOriginalFourier.fullCoefficients f (2*m))))

def quarterEntire (m : ℕ) (f : ℕ→ℂ) : ℂ→ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1
    (quarterCoefficients (FinitenessOriginalFourier.fullCoefficients f (2*m))))

/-- Conditional on the P law, the quarter difference has an entire finite-order Mellin transform and
its conductor-208 functional equation, directly from original input. -/
theorem original_quarter_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 26 (by decide)=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (hP : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 26 f 2 • SmallLevelOriginal.fourierFunction (2*m) f) :
      Differentiable ℂ (quarterMellin m f) ∧
      FinitenessFiniteOrder.Bound (quarterMellin m f) ∧
      ∀ s : ℂ, quarterMellin m f s=
        ((-(FinitenessNormalizedTwistProduct.root 26 f 2*η))/(Complex.I^(2*m)))*quarterMellin m f ((2*m:ℕ)-s) := by
  obtain ⟨hn,hp⟩:=quarter_fricke_of_P m _ _ η (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2) hη hW hP
  have hχ : -(FinitenessNormalizedTwistProduct.root 26 f 2*η)=1 ∨ -(FinitenessNormalizedTwistProduct.root 26 f 2*η)= -1 := by
    rcases FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2 with h|h <;>
      rcases hη with h'|h' <;> simp [h,h']
  obtain ⟨τ,_,hg⟩:=hf.growth
  let a:=FinitenessOriginalFourier.fullCoefficients f (2*m)
  have ha : PolynomialBound a:=FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m)
  have ha0 : a 0=0:=FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)
  have hB0 : quarterCoefficients a 0=0 := by simp [quarterCoefficients,coefficients_zero ha0]
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ:=((2*m:ℕ):ℤ)
  have hfourier : (fun z : ℍ => fourier (quarterCoefficients a) z)=
      (F ∣[k] translation (1/4))-(F ∣[k] translation (-1/4)) := by
    funext z
    rw [quarter_fourier ha z z.im_pos]
    simp only [Pi.sub_apply,translation_slash]
    change fourier a _-fourier a _=fourier a ((translation (1/4) • z:ℍ):ℂ)-
      fourier a ((translation (-1/4) • z:ℍ):ℂ)
    rw [translation_point,translation_point]
  have hslash : (fun z : ℍ => fourier (quarterCoefficients a) z) ∣[k] fricke 208 (by decide)=
      (-(FinitenessNormalizedTwistProduct.root 26 f 2*η)) • (fun z : ℍ => fourier (quarterCoefficients a) z) := by
    rw [hfourier,sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash,hp,hn]
    simp only [_root_.neg_smul,smul_add,smul_neg]
    abel
  have hl:=formula_of_slash 208 (2*m) (by decide) (fourier (quarterCoefficients a)) (-(FinitenessNormalizedTwistProduct.root 26 f 2*η)) hχ hslash
  have hχ0 : -(FinitenessNormalizedTwistProduct.root 26 f 2*η)≠0 := by
    rcases hχ with h|h <;> rw [h] <;> norm_num
  apply FinitenessAllLevelMellinPair.mellin_entire (by decide : 0<208) (by omega : 0<2*m)
    (quarterCoefficients a) (quarter_polynomial ha) hB0 ((-(FinitenessNormalizedTwistProduct.root 26 f 2*η))/(Complex.I^(2*m)))
    (div_ne_zero hχ0 (pow_ne_zero _ Complex.I_ne_zero))
  simpa only [div_mul_cancel₀ _ (pow_ne_zero (2*m) Complex.I_ne_zero)] using hl

/-- The entire unscaled even-quarter continuation agrees with the literal
difference of the two additive Dirichlet series in an initial half-plane. -/
theorem original_quarter_continuation (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 26 (by decide)=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (hP : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 26 f 2 • SmallLevelOriginal.fourierFunction (2*m) f) :
    Differentiable ℂ (quarterEntire m f) ∧
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → quarterEntire m f s=
      original (2*m) f (1/4) s-original (2*m) f (-1/4) s := by
  obtain ⟨he,_,_⟩:=original_quarter_entire m hm hf η hη hW hP
  refine ⟨QuantitativeArithmeticMellinScale.entire_at_one (by decide : 0<208) _ he,?_⟩
  obtain ⟨τ,_,hg⟩:=hf.growth
  let a:=FinitenessOriginalFourier.fullCoefficients f (2*m)
  have ha : PolynomialBound a:=FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m)
  have ha0 : a 0=0:=FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)
  have hB0 : quarterCoefficients a 0=0 := by simp [quarterCoefficients,coefficients_zero ha0]
  obtain ⟨B,hB⟩:=common_halfplane (quarter_polynomial ha) hB0
  obtain ⟨d,hd⟩:=FinitenessAllLevelMellinDirichlet.polynomial_growth ha
  refine ⟨max B ((d:ℝ)+1),fun s hs => ?_⟩
  have hsB : B<s.re := (le_max_left _ _).trans_lt hs
  have hsd : (d:ℝ)+1<s.re := (le_max_right _ _).trans_lt hs
  have hh:=(hB 0 s hsB).2
  have hc0 : coefficients (quarterCoefficients a) 0=quarterCoefficients a := by
    funext n
    simp [coefficients,phase]
  have hL : LSeries (quarterCoefficients a) s=
      LSeries (coefficients a (1/4)) s-LSeries (coefficients a (-1/4)) s :=
    LSeries_sub (summable_at hd _ hsd) (summable_at hd _ hsd)
  change quarterEntire m f s=transform a (1/4) s-transform a (-1/4) s
  have hmain : quarterEntire m f s=transform (quarterCoefficients a) 0 s := by
    have haxis : FinitenessAllLevelAxisDecay.axis 1 (quarterCoefficients a)=
        (fun t : ℝ => fourier (quarterCoefficients a) ((t:ℂ)*Complex.I)) := by
      funext t
      simp [FinitenessAllLevelAxisDecay.axis]
    change mellin (FinitenessAllLevelAxisDecay.axis 1 (quarterCoefficients a)) s=_
    rw [haxis]
    simpa only [Complex.ofReal_zero,zero_add] using hh
  rw [hmain,transform,hc0,hL,transform,transform]
  ring

#print axioms original_quarter_entire
#print axioms original_quarter_continuation
end SmallLevelTwentySixQuarter
end
end
