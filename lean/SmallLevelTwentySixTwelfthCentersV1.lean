module

public import SmallLevelRamifiedTwoRootV1
public import SmallLevelSixRootsV1
public import SmallLevelTwentyEightTwelfthCentersV1
public import QuantitativeArithmeticTranslatedFrickeTheoryV4
public import QuantitativeArithmeticMellinScaleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixTwelfth
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelGenerators
  QuantitativeArithmeticTranslatedFricke FinitenessPolynomialSeries FinitenessFourierConstruction
  SmallLevelAdditive Complex MeasureTheory
open scoped MatrixGroups ModularForm

def E : GL (Fin 2) ℝ :=
  matrix (2/Real.sqrt 2) (-1/Real.sqrt 2) (-26/Real.sqrt 2) (14/Real.sqrt 2) (by
    have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    field_simp [SmallLevelRamifiedTwo.sqrt_two_ne]
    nlinarith)

def W : GL (Fin 2) ℝ := fricke 26 (by decide)

theorem E_det : (GeneralLinearGroup.det E:ℝ)=1 := matrix_det _ _ _ _ _

theorem E_inverse : E=(SmallLevelRamifiedTwo.Q 26 14 (by decide))⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).mpr
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E,SmallLevelRamifiedTwo.Q,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [SmallLevelRamifiedTwo.sqrt_two_ne] <;> nlinarith

theorem original_E {k : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] E=
      FinitenessNormalizedTwistProduct.root 26 f 2 • SmallLevelOriginal.fourierFunction k f := by
  rw [E_inverse]
  exact SmallLevelSixEigen.eigen_inverse _ _ _ (SmallLevelRamifiedTwo.Q_det _ _ _)
    _ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2)
    (SmallLevelRamifiedTwo.original_eigen_root (by decide : 0<26) (by decide : 2*14=26+2)
      (by decide : Nat.lcm 26 (2^2)=2*26) hf)

private theorem sqrt_1872 : Real.sqrt 1872=6*Real.sqrt 26*Real.sqrt 2 := by
  rw [mul_assoc,← Real.sqrt_mul (by norm_num : (0:ℝ)≤26)]
  rw [show (1872:ℝ)=36*(26*2) by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

/-- The known elementary matrices exchange the two twelfth centers. -/
theorem twelfth_branch : E*translation 1*W=
    (-1:GL (Fin 2) ℝ)*translation (-1/12)*fricke 1872 (by decide)*translation (-1/12) := by
  have hs : (Real.sqrt 26)^2=26 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 26≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E,W,fricke,translation,sqrt_1872,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn,SmallLevelRamifiedTwo.sqrt_two_ne] <;> norm_num [hs,ht]

/-- Actual exchanged Fricke laws at the two twelfth centers, with the
same original sign product. No additive continuation is assumed. -/
theorem original_twelfth_fricke (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f) :
      let F:=SmallLevelOriginal.fourierFunction (2*m) f
      ((F ∣[((2*m:ℕ):ℤ)] translation (-1/12)) ∣[((2*m:ℕ):ℤ)] fricke 1872 (by decide)=
        (FinitenessNormalizedTwistProduct.root 26 f 2*η) • (F ∣[((2*m:ℕ):ℤ)] translation (1/12))) ∧
      ((F ∣[((2*m:ℕ):ℤ)] translation (1/12)) ∣[((2*m:ℕ):ℤ)] fricke 1872 (by decide)=
        (FinitenessNormalizedTwistProduct.root 26 f 2*η) • (F ∣[((2*m:ℕ):ℤ)] translation (-1/12))) := by
  have hE:=original_E hf
  let δ : ℂ:=FinitenessNormalizedTwistProduct.root 26 f 2
  have hδ : δ=1 ∨ δ= -1 := FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2
  have hc : δ*η=1 ∨ δ*η= -1 := by
    rcases hδ with h|h <;> rcases hη with h'|h' <;> simp [h,h']
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
  change F ∣[k] E=δ • F at hE
  rw [SlashAction.slash_mul,SlashAction.slash_mul,hE,
    det_one_smul _ (translation_det _),hT,det_one_smul _ (show (GeneralLinearGroup.det W:ℝ)=1 from fricke_det 26 (by decide)),hW,
    smul_smul] at hh
  simp only [SlashAction.slash_mul,hZ] at hh
  have hn:=congrArg (fun G : ℍ→ℂ => G ∣[k] translation (1/12)) hh
  rw [det_one_smul _ (translation_det _),← SlashAction.slash_mul,translation_mul,
    show (-1/12:ℝ)+1/12=0 by ring] at hn
  have ht0 : translation 0=(1:GL (Fin 2) ℝ) := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]
  rw [ht0,SlashAction.slash_one] at hn
  have hp:=congrArg (fun G : ℍ→ℂ => G ∣[k] fricke 1872 (by decide)) hn
  rw [det_one_smul _ (fricke_det _ _)] at hp
  have hsquare : fricke 1872 (by decide)*fricke 1872 (by decide)=(-1:GL (Fin 2) ℝ) := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply,Fin.sum_univ_two]
    field_simp
  have he : ((F ∣[k] translation (-1/12)) ∣[k] fricke 1872 (by decide))
      ∣[k] fricke 1872 (by decide)=F ∣[k] translation (-1/12) := by
    rw [← SlashAction.slash_mul,hsquare]
    exact central_even _ m
  rw [he] at hp
  refine ⟨hn.symm,?_⟩
  change (F ∣[k] translation (1/12)) ∣[k] fricke 1872 (by decide)=
    (δ*η) • (F ∣[k] translation (-1/12))
  rcases hc with hc|hc
  · simpa only [hc,one_smul] using hp
  · simpa only [hc,neg_one_smul,neg_neg] using congrArg Neg.neg hp

#print axioms original_E
#print axioms original_twelfth_fricke
end SmallLevelTwentySixTwelfth
