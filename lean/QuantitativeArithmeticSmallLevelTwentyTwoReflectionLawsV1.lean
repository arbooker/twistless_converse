module

public import QuantitativeArithmeticSmallLevelTwentyTwoPoleLocusV1
public import QuantitativeArithmeticQuadraticTwistReflectionTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelGenerators
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct FinitenessRamanujanFourier FinitenessAllLevelAxisDecay
open QuantitativeArithmeticTranslatedFricke FinitenessPolynomialSeries SmallLevelAdditive
open Complex MeasureTheory
open scoped MatrixGroups ModularForm

theorem root_two (f : ℕ → ℂ) : root 22 f 2= -(f 2*(Real.sqrt 2:ℂ)) := by
  simp [root,(by decide : Nat.Prime 2).primeFactors,FinitenessNormalizedTwistLocal.sign,
    show (2:ℕ)∣22 by decide, Nat.prime_two.factorization_self]

theorem root_five (f : ℕ → ℂ) : root 22 f 5=1 := by
  simp [root,(by decide : Nat.Prime 5).primeFactors,FinitenessNormalizedTwistLocal.sign]

/-- The exact center exchange retains both specified original signs. -/
theorem tenth_fricke_of_signs (m : ℕ) (f : ℕ → ℂ) (δ η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hE : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] E=
      δ • SmallLevelOriginal.fourierFunction (2*m) f)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f) :
    let F:=SmallLevelOriginal.fourierFunction (2*m) f
    ((F ∣[((2*m:ℕ):ℤ)] translation (-1/10)) ∣[((2*m:ℕ):ℤ)] fricke 1100 (by decide)=
      (δ*η) • (F ∣[((2*m:ℕ):ℤ)] translation (1/10))) ∧
    ((F ∣[((2*m:ℕ):ℤ)] translation (1/10)) ∣[((2*m:ℕ):ℤ)] fricke 1100 (by decide)=
      (δ*η) • (F ∣[((2*m:ℕ):ℤ)] translation (-1/10))) := by
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ:=((2*m:ℕ):ℤ)
  have hχ : δ*η=1 ∨ δ*η= -1 := by
    rcases hδ with rfl|rfl <;> rcases hη with rfl|rfl <;> norm_num
  have hT : F ∣[k] translation 1=F := by
    have ht : translation 1=SpecialLinearGroup.mapGL ℝ T := by
      apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero,T,
          SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
    rw [ht]
    exact original_T _ _
  have hZ : F ∣[k] (-1:GL (Fin 2) ℝ)=F := central_even F m
  change F ∣[k] W=η • F at hW
  have hh:=congrArg (fun M : GL (Fin 2) ℝ => F ∣[k] M) tenth_branch
  rw [SlashAction.slash_mul,SlashAction.slash_mul,hE,
    det_one_smul _ (translation_det _),hT,det_one_smul _ (show (GeneralLinearGroup.det W:ℝ)=1 from fricke_det _ _),hW,
    smul_smul] at hh
  simp only [SlashAction.slash_mul,hZ] at hh
  have hn:=congrArg (fun G : ℍ→ℂ => G ∣[k] translation (1/10)) hh
  rw [det_one_smul _ (translation_det _),← SlashAction.slash_mul,translation_mul,
    show (-1/10:ℝ)+1/10=0 by ring] at hn
  have ht0 : translation 0=(1:GL (Fin 2) ℝ) := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]
  rw [ht0,SlashAction.slash_one] at hn
  have hp:=congrArg (fun G : ℍ→ℂ => G ∣[k] fricke 1100 (by decide)) hn
  rw [det_one_smul _ (fricke_det _ _)] at hp
  have hsquare : fricke 1100 (by decide)*fricke 1100 (by decide)=(-1:GL (Fin 2) ℝ) := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply,Fin.sum_univ_two]
    field_simp
  have he : ((F ∣[k] translation (-1/10)) ∣[k] fricke 1100 (by decide))
      ∣[k] fricke 1100 (by decide)=F ∣[k] translation (-1/10) := by
    rw [← SlashAction.slash_mul,hsquare]
    exact central_even _ m
  rw [he] at hp
  refine ⟨hn.symm,?_⟩
  rcases hχ with hc|hc
  · simpa only [hc,one_smul] using hp
  · simpa only [hc,neg_one_smul,neg_neg] using congrArg Neg.neg hp

/-- One original functional-equation sign controls both Mellin pieces.
The conductor-1100 even sum has sign root(2)*epsilon. -/
theorem original_scaled_reflections (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : IsSolution 22 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      (∀ s : ℂ, tenthMellin m f s=(root 22 f 2*ε)*tenthMellin m f ((2*m:ℕ)-s)) ∧
      (∀ s : ℂ, mellin (axis 550 (fullCoefficients (twisted f 5) (2*m))) s=
        ε*mellin (axis 550 (fullCoefficients (twisted f 5) (2*m))) ((2*m:ℕ)-s)) := by
  obtain ⟨ε,hε,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<22) hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  let χ : ℂ := ε*Complex.I^(2*m)
  let δ : ℂ := root 22 f 2
  have hδ : δ=1 ∨ δ= -1 := root_unit hf.toEulerData 2
  have hχ : χ=1 ∨ χ= -1 := by
    have hi : Complex.I^(2*m)=(-1:ℂ)^m := by rw [pow_mul,Complex.I_sq]
    rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hε with rfl|rfl <;> simp [χ,hi,h]
  have hfr : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients f (2*m)) z=
      χ/(((Real.sqrt 22:ℂ)*z)^(2*m))*fourier (fullCoefficients f (2*m)) (-1/((22:ℂ)*z)) := by
    intro z hz
    simpa [χ,root,FinitenessAnalyticReconstruction.twist,Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  have hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      χ • SmallLevelOriginal.fourierFunction (2*m) f := by
    have h:=fricke_law 22 (2*m) (by decide) (fourier (fullCoefficients f (2*m))) χ hfr
    change SmallLevelOriginal.fourierFunction (2*m) f=
      χ • (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W) at h
    rcases hχ with hc|hc
    · rw [hc] at h ⊢; simpa using h.symm
    · rw [hc] at h ⊢; simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg h.symm
  have hQ : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      SmallLevelRamifiedTwo.Q 22 12 (by decide)=δ • SmallLevelOriginal.fourierFunction (2*m) f := by
    apply SmallLevelRamifiedTwo.eigen_of_fricke (by decide : 0<22) (by decide : 2*12=22+2) _ χ δ hfr
    intro z hz
    have h:=hlaw 2 (by decide) z hz
    have ht (G : ℂ → ℂ) (w : ℂ) : FinitenessAnalyticReconstruction.twist G 2 w=G (w+1/2) := by
      unfold FinitenessAnalyticReconstruction.twist
      rw [show (Finset.range 2).filter (fun a => Nat.Coprime a 2)={1} by decide]
      simp
    have hsqrt : Real.sqrt 44=Real.sqrt 2*Real.sqrt 22 := by
      rw [show (44:ℝ)=2*22 by norm_num,Real.sqrt_mul (by norm_num)]
    rw [show Nat.lcm 22 (2^2)=44 by decide,Nat.cast_ofNat,hsqrt,Complex.ofReal_mul,ht,ht] at h
    simpa only [δ,χ,Nat.cast_ofNat,mul_assoc,show (44:ℂ)=2*22 by norm_num] using h
  have hE : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] E=
      δ • SmallLevelOriginal.fourierFunction (2*m) f := by
    have hh:=congrArg (fun F : ℍ → ℂ => F ∣[((2*m:ℕ):ℤ)] E) hQ
    rw [← SlashAction.slash_mul,show SmallLevelRamifiedTwo.Q 22 12 (by decide)*E=1 from mul_inv_cancel _,
      SlashAction.slash_one,det_one_smul _ E_det] at hh
    rcases hδ with hc|hc
    · rw [hc] at hh ⊢; simpa using hh.symm
    · rw [hc] at hh ⊢; simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg hh.symm
  obtain ⟨hn,hp⟩:=tenth_fricke_of_signs m f δ χ hδ hχ hE hW
  have hδχ : δ*χ=1 ∨ δ*χ= -1 := by
    rcases hδ with h|h <;> rcases hχ with h'|h' <;> simp [h,h']
  refine ⟨ε,hε,?_,?_⟩
  · let a:=fullCoefficients f (2*m)
    have ha : PolynomialBound a:=polynomial_bound hf.zero hg (2*m)
    have ha0 : a 0=0:=fullCoefficients_zero hf.zero (2*m)
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
        (δ*χ) • (fun z : ℍ => fourier (tenthCoefficients a) z) := by
      rw [hfourier,SlashAction.add_slash,hp,hn,← smul_add]
      congr 1
      abel
    have hl:=formula_of_slash 1100 (2*m) (by decide) (fourier (tenthCoefficients a)) (δ*χ) hδχ hslash
    have hc0 : δ*χ≠0 := by rcases hδχ with h|h <;> rw [h] <;> norm_num
    have he:=FinitenessAllLevelMellinPair.mellin_entire (by decide : 0<1100) (by omega : 0<2*m)
      (tenthCoefficients a) (tenth_polynomial ha) hB0 ((δ*χ)/(Complex.I^(2*m)))
      (div_ne_zero hc0 (pow_ne_zero _ Complex.I_ne_zero)) (by
        simpa only [div_mul_cancel₀ _ (pow_ne_zero (2*m) Complex.I_ne_zero)] using hl)
    intro s
    have hh:=he.2.2 s
    have hsign : (δ*χ)/Complex.I^(2*m)=δ*ε := by
      dsimp [χ]
      rw [← mul_assoc,mul_div_cancel_right₀ _ (pow_ne_zero _ Complex.I_ne_zero)]
    simpa only [hsign,δ,a,tenthMellin] using hh
  · have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
    have hfr5 : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients (twisted f 5) (2*m)) z=
        (ε*Complex.I^(2*m))/(((Real.sqrt 550:ℂ)*z)^(2*m))*
          fourier (fullCoefficients (twisted f 5) (2*m)) (-1/((550:ℂ)*z)) := by
      intro z hz
      have href : 0<(-1/((550:ℂ)*z)).im :=
        FinitenessComplexGeometry.reflected_im_pos (by norm_num : (0:ℝ)<550) hz
      simpa only [fourier_twisted hf.zero hg 5 (2*m) hz,
        fourier_twisted hf.zero hg 5 (2*m) href,show Nat.lcm 22 (5^2)=550 by decide,
        root_five,one_mul,mul_assoc,Nat.cast_ofNat] using hlaw 5 (by decide) z hz
    exact (FinitenessAllLevelMellinPair.mellin_entire (by decide : 0<550) (by omega) _
      (polynomial_bound (twisted_zero hf.zero 5) (twisted_growth hg 5) (2*m))
      (fullCoefficients_zero (twisted_zero hf.zero 5) (2*m)) ε hε0 hfr5).2.2

theorem original_unscaled_reflections (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : IsSolution 22 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      (∀ s : ℂ, evenTenthEntire m f s=(root 22 f 2*ε)*(Real.sqrt 1100:ℂ)^((2*m:ℕ)-2*s)*
        evenTenthEntire m f ((2*m:ℕ)-s)) ∧
      (∀ s : ℂ, SmallLevelTaylor.ramanujanEntire 22 (2*m) f 5 s=
        ε*(Real.sqrt 550:ℂ)^((2*m:ℕ)-2*s)*SmallLevelTaylor.ramanujanEntire 22 (2*m) f 5 ((2*m:ℕ)-s)) := by
  obtain ⟨ε,hε,hc,hr⟩:=original_scaled_reflections m hm hf
  refine ⟨ε,hε,QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection
    (by decide : 0<1100) _ (root 22 f 2*ε) hc,?_⟩
  intro s
  have h:=QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection (by decide : 0<550) _ ε hr s
  have haxis : axis 1 (fullCoefficients (twisted f 5) (2*m))=
      (fun y : ℝ => fourier (fullCoefficients (twisted f 5) (2*m)) ((y:ℂ)*Complex.I)) := by
    funext y
    simp [axis]
  rw [haxis] at h
  simpa only [SmallLevelTaylor.ramanujanEntire,Nat.cast_ofNat] using h

#print axioms tenth_fricke_of_signs
#print axioms original_scaled_reflections
#print axioms original_unscaled_reflections
end QuantitativeArithmeticSmallLevelTwentyTwo
