module

public import QuantitativeArithmeticSmallLevelNineteenPairsV1
public import SmallLevelNormalizedEvenFrickeV1
public import SmallLevelTaylorTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelNineteen
open Matrix ModularGroup UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open SmallLevelOriginal Complex
open scoped MatrixGroups ModularForm

def tenthMinus : SL(2,ℤ) := (oddMatrix 19 10 (by decide))⁻¹
def tenthPlus : SL(2,ℤ) := lower 19*tenthMinus*T

theorem tenthMinus_matrix : tenthMinus=(⟨!![2,-1;-19,10],by decide⟩ : SL(2,ℤ)) := by decide
theorem tenthPlus_matrix : tenthPlus=(⟨!![2,1;19,10],by decide⟩ : SL(2,ℤ)) := by decide

theorem original_tenth_matrices {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 k f) :
    fourierFunction k f ∣[(k:ℤ)] tenthMinus=fourierFunction k f ∧
    fourierFunction k f ∣[(k:ℤ)] tenthPlus=fourierFunction k f := by
  let K := slashStabilizer (k:ℤ) (fourierFunction k f)
  have ho : oddMatrix 19 10 (by decide)∈K := original_odd (by decide) (by decide) (by decide) hf
  have hm : tenthMinus∈K := K.inv_mem ho
  have hu : lower 19∈K := original_lower (by decide) hf
  have ht : T∈K := original_T k f
  exact ⟨hm,K.mul_mem (K.mul_mem hu hm) ht⟩

theorem sqrt_nineteen_hundred : Real.sqrt 1900=10*Real.sqrt 19 := by
  rw [show (1900:ℝ)=100*19 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem tenth_positive_factor :
    translation (1/10)*fricke 1900 (by decide)=
      SpecialLinearGroup.mapGL ℝ tenthPlus*fricke 19 (by decide)*translation (1/10) := by
  rw [tenthPlus_matrix]
  have hs : (Real.sqrt 19)^2=19 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 19≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,translation,SmallLevelNormalized.matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_nineteen_hundred] <;>
    field_simp [hn] <;> norm_num [hs]

theorem tenth_negative_factor :
    translation (-1/10)*fricke 1900 (by decide)=
      SpecialLinearGroup.mapGL ℝ tenthMinus*fricke 19 (by decide)*translation (-1/10) := by
  rw [tenthMinus_matrix]
  have hs : (Real.sqrt 19)^2=19 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 19≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,translation,SmallLevelNormalized.matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_nineteen_hundred] <;>
    field_simp [hn] <;> norm_num [hs]

/-- Both individual tenth-translates satisfy genuine Fricke laws from the
original Euler input; no grid continuation or quadratic twist is assumed. -/
theorem original_tenth_fricke (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧
      ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (1/10)) ∣[((2*m:ℕ):ℤ)]
        fricke 1900 (by decide))=χ • (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (1/10)) ∧
      ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (-1/10)) ∣[((2*m:ℕ):ℤ)]
        fricke 1900 (by decide))=χ • (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (-1/10)) := by
  obtain ⟨χ,hχ,hfr⟩ := original_fricke_sign (by decide : 0<19) m hf
  obtain ⟨hm,hp⟩ := original_tenth_matrices hf
  refine ⟨χ,hχ,?_,?_⟩
  · rw [← SlashAction.slash_mul,tenth_positive_factor,SlashAction.slash_mul,SlashAction.slash_mul]
    change ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] tenthPlus) ∣[((2*m:ℕ):ℤ)]
      fricke 19 (by decide)) ∣[((2*m:ℕ):ℤ)] translation (1/10)=_
    rw [hp,hfr,det_one_smul _ (translation_det _)]
  · rw [← SlashAction.slash_mul,tenth_negative_factor,SlashAction.slash_mul,SlashAction.slash_mul]
    change ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] tenthMinus) ∣[((2*m:ℕ):ℤ)]
      fricke 19 (by decide)) ∣[((2*m:ℕ):ℤ)] translation (-1/10)=_
    rw [hm,hfr,det_one_smul _ (translation_det _)]

#print axioms original_tenth_matrices
#print axioms original_tenth_fricke
end QuantitativeArithmeticSmallLevelNineteen
