module

public import SmallLevelTwentyEightGridWordRowsV1
public import QuantitativeArithmeticTranslatedFrickeTheoryV4
public import QuantitativeArithmeticMellinScaleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightTwelfth
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelGenerators
  QuantitativeArithmeticTranslatedFricke FinitenessPolynomialSeries FinitenessFourierConstruction
  SmallLevelAdditive Complex MeasureTheory
open scoped MatrixGroups ModularForm

open SmallLevelTwentyEightGenerators (E W)

private theorem sqrt_1008 : Real.sqrt 1008=6*Real.sqrt 28 := by
  have h1 : (Real.sqrt 1008)^2=1008 := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 28)^2=28 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (1008:ℝ),Real.sqrt_nonneg (28:ℝ)]

/-- The known elementary matrices exchange the two twelfth centers. -/
theorem twelfth_branch : E*translation 1*W=
    (-1:GL (Fin 2) ℝ)*translation (-1/12)*fricke 1008 (by decide)*translation (-1/12) := by
  have hs : (Real.sqrt 28)^2=28 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 28≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E,W,fricke,translation,sqrt_1008,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

/-- Actual exchanged Fricke laws at the two twelfth centers, with the
same original sign product. No additive continuation is assumed. -/
theorem original_twelfth_fricke (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f)
    (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f) :
      let F:=SmallLevelOriginal.fourierFunction (2*m) f
      ((F ∣[((2*m:ℕ):ℤ)] translation (-1/12)) ∣[((2*m:ℕ):ℤ)] fricke 1008 (by decide)=
        η • (F ∣[((2*m:ℕ):ℤ)] translation (1/12))) ∧
      ((F ∣[((2*m:ℕ):ℤ)] translation (1/12)) ∣[((2*m:ℕ):ℤ)] fricke 1008 (by decide)=
        η • (F ∣[((2*m:ℕ):ℤ)] translation (-1/12))) := by
  have hE:=(SmallLevelTwentyEightGenerators.original_generators m hf η hη hW).2
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ:=((2*m:ℕ):ℤ)
  have hT : F ∣[k] translation 1=F := by
    have ht : translation 1=SpecialLinearGroup.mapGL ℝ T := by
      apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero,T,
          SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
    rw [ht]
    exact original_T _ _
  have hZ : F ∣[k] (-1:GL (Fin 2) ℝ)=F := central_even F m
  change F ∣[k] W=η • F at hW
  have hh:=congrArg (fun M : GL (Fin 2) ℝ => F ∣[k] M) twelfth_branch
  rw [SlashAction.slash_mul,SlashAction.slash_mul,hE,hT,hW] at hh
  simp only [SlashAction.slash_mul,hZ] at hh
  have hn:=congrArg (fun G : ℍ→ℂ => G ∣[k] translation (1/12)) hh
  rw [det_one_smul _ (translation_det _),← SlashAction.slash_mul,translation_mul,
    show (-1/12:ℝ)+1/12=0 by ring] at hn
  have ht0 : translation 0=(1:GL (Fin 2) ℝ) := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]
  rw [ht0,SlashAction.slash_one] at hn
  have hp:=congrArg (fun G : ℍ→ℂ => G ∣[k] fricke 1008 (by decide)) hn
  rw [det_one_smul _ (fricke_det _ _)] at hp
  have hsquare : fricke 1008 (by decide)*fricke 1008 (by decide)=(-1:GL (Fin 2) ℝ) := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply,Fin.sum_univ_two]
    field_simp
  have he : ((F ∣[k] translation (-1/12)) ∣[k] fricke 1008 (by decide))
      ∣[k] fricke 1008 (by decide)=F ∣[k] translation (-1/12) := by
    rw [← SlashAction.slash_mul,hsquare]
    exact central_even _ m
  rw [he] at hp
  refine ⟨hn.symm,?_⟩
  rcases hη with hc|hc
  · simpa only [hc,one_smul] using hp
  · simpa only [hc,neg_one_smul,neg_neg] using congrArg Neg.neg hp

def twelfthCoefficients (a : ℕ→ℂ) (n : ℕ) : ℂ :=
  coefficients a (1/12) n-coefficients a (-1/12) n

theorem twelfth_polynomial {a : ℕ→ℂ} (ha : PolynomialBound a) : PolynomialBound (twelfthCoefficients a) := by
  obtain ⟨C,hC,d,hd⟩:=ha
  refine ⟨2*C,by positivity,d,fun n => ?_⟩
  calc
    ‖twelfthCoefficients a n‖ ≤ ‖coefficients a (1/12) n‖+‖coefficients a (-1/12) n‖ := norm_sub_le _ _
    _ ≤ C*(1+(n:ℝ)^d)+C*(1+(n:ℝ)^d) := by simpa only [coefficients_norm] using add_le_add (hd n) (hd n)
    _ = 2*C*(1+(n:ℝ)^d) := by ring

theorem twelfth_fourier {a : ℕ→ℂ} (ha : PolynomialBound a) (z : ℂ) (hz : 0<z.im) :
    fourier (twelfthCoefficients a) z=fourier a (z+(1/12:ℝ))-fourier a (z+(-1/12:ℝ)) := by
  rw [← fourier_translate,← fourier_translate]
  simp only [fourier,sum_eq_tsum]
  simp only [twelfthCoefficients,sub_mul]
  exact (summable (coefficients_polynomial ha _) (Function.Periodic.norm_qParam_lt_one (by norm_num) hz)).tsum_sub
    (summable (coefficients_polynomial ha _) (Function.Periodic.norm_qParam_lt_one (by norm_num) hz))

#print axioms original_twelfth_fricke
#print axioms twelfth_fourier
end SmallLevelTwentyEightTwelfth
