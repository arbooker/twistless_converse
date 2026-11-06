module

public import QuantitativeArithmeticSmallLevelTwentyTwoDefectV1
public import QuantitativeArithmeticTranslatedFrickeTheoryV4
public import QuantitativeArithmeticMellinScaleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelGenerators
  QuantitativeArithmeticTranslatedFricke FinitenessPolynomialSeries FinitenessFourierConstruction
  SmallLevelAdditive Complex MeasureTheory
open scoped MatrixGroups ModularForm

private theorem sqrt_1100 : Real.sqrt 1100=5*Real.sqrt 2*Real.sqrt 22 := by
  have h1 : (Real.sqrt 1100)^2=1100 := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have hp : 0<5*Real.sqrt 2*Real.sqrt 22 := by positivity
  nlinarith [sq_nonneg (Real.sqrt 1100+5*Real.sqrt 2*Real.sqrt 22),
    congrArg (fun x : ℝ => x*(Real.sqrt 22)^2) h2,
    Real.sqrt_nonneg (1100:ℝ)]

/-- The known elementary matrices exchange the two tenth centers. -/
theorem tenth_branch : E*translation 1*W=
    (-1:GL (Fin 2) ℝ)*translation (-1/10)*fricke 1100 (by decide)*translation (-1/10) := by
  rw [E_explicit]
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [W,fricke,translation,sqrt_1100,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn,hn2] <;> nlinarith

/-- Actual exchanged Fricke laws at the two tenth centers, with the
same original sign product. No additive continuation is assumed. -/
theorem original_tenth_fricke (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧
      let F:=SmallLevelOriginal.fourierFunction (2*m) f
      ((F ∣[((2*m:ℕ):ℤ)] translation (-1/10)) ∣[((2*m:ℕ):ℤ)] fricke 1100 (by decide)=
        χ • (F ∣[((2*m:ℕ):ℤ)] translation (1/10))) ∧
      ((F ∣[((2*m:ℕ):ℤ)] translation (1/10)) ∣[((2*m:ℕ):ℤ)] fricke 1100 (by decide)=
        χ • (F ∣[((2*m:ℕ):ℤ)] translation (-1/10))) := by
  obtain ⟨δ,hδ,hE⟩:=original_E hf
  obtain ⟨η,hη,hW⟩:=original_fricke_sign (by decide : 0<22) m hf
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ:=((2*m:ℕ):ℤ)
  have hχ : δ*η=1 ∨ δ*η= -1 := by
    rcases hδ with rfl|rfl <;> rcases hη with rfl|rfl <;> norm_num
  refine ⟨δ*η,hχ,?_⟩
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

def tenthCoefficients (a : ℕ→ℂ) (n : ℕ) : ℂ :=
  coefficients a (1/10) n+coefficients a (-1/10) n

theorem tenth_polynomial {a : ℕ→ℂ} (ha : PolynomialBound a) : PolynomialBound (tenthCoefficients a) := by
  obtain ⟨C,hC,d,hd⟩:=ha
  refine ⟨2*C,by positivity,d,fun n => ?_⟩
  calc
    ‖tenthCoefficients a n‖ ≤ ‖coefficients a (1/10) n‖+‖coefficients a (-1/10) n‖ := norm_add_le _ _
    _ ≤ C*(1+(n:ℝ)^d)+C*(1+(n:ℝ)^d) := by simpa only [coefficients_norm] using add_le_add (hd n) (hd n)
    _ = 2*C*(1+(n:ℝ)^d) := by ring

theorem tenth_fourier {a : ℕ→ℂ} (ha : PolynomialBound a) (z : ℂ) (hz : 0<z.im) :
    fourier (tenthCoefficients a) z=fourier a (z+(1/10:ℝ))+fourier a (z+(-1/10:ℝ)) := by
  rw [← fourier_translate,← fourier_translate]
  simp only [fourier,sum_eq_tsum]
  simp only [tenthCoefficients,add_mul]
  exact (summable (coefficients_polynomial ha _) (Function.Periodic.norm_qParam_lt_one (by norm_num) hz)).tsum_add
    (summable (coefficients_polynomial ha _) (Function.Periodic.norm_qParam_lt_one (by norm_num) hz))

#print axioms original_tenth_fricke
#print axioms tenth_fourier
end QuantitativeArithmeticSmallLevelTwentyTwo
