module

public import QuantitativeArithmeticOriginalMatrixMellinTheoryV4
public import QuantitativeArithmeticTwoSequenceTaylorTheoryV4
public import SmallLevelNormalizedEvenFrickeV1
public import SmallLevelOddFrickeV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenKnownWords. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenKnownWordsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenKnownWords
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

/-- The three determinant-one generators in the level27 source system. -/
def seed : Fin 3 → SL(2,ℤ)
  | 0 => T
  | 1 => lower 27
  | _ => (oddMatrix 27 14 (by decide))⁻¹

inductive Word where
  | one : Word
  | generator : Fin 3 → Word
  | mul : Word → Word → Word
  | inv : Word → Word

def value : Word → SL(2,ℤ)
  | .one => 1
  | .generator i => seed i
  | .mul u v => value u*value v
  | .inv w => (value w)⁻¹

theorem original_seeds {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 k f) (i : Fin 3) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] seed i=
      SmallLevelOriginal.fourierFunction k f := by
  let K := slashStabilizer (k:ℤ) (SmallLevelOriginal.fourierFunction k f)
  have ho : (oddMatrix 27 14 (by decide))⁻¹∈K := K.inv_mem
    (original_odd (by decide) (by decide : 2*14=27+1) (by decide) hf)
  fin_cases i
  · exact original_T k f
  · exact original_lower (by decide : 0<27) hf
  · exact ho

/-- Actual modularity under every known word, before any additional twist
continuation is established. -/
theorem original_words {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 k f) (w : Word) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] value w=
      SmallLevelOriginal.fourierFunction k f := by
  let K := slashStabilizer (k:ℤ) (SmallLevelOriginal.fourierFunction k f)
  change value w∈K
  induction w with
  | one => exact K.one_mem
  | generator i => exact original_seeds hf i
  | mul u v hu hv => exact K.mul_mem hu hv
  | inv w hw => exact K.inv_mem hw

#print axioms original_seeds
#print axioms original_words
end QuantitativeArithmeticSmallLevelTwentySevenKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenKnownWordFourierV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenKnownWords
open Matrix UpperHalfPlane SmallLevelNormalized Complex Set
open FinitenessOriginalFourier FinitenessFourierConstruction SmallLevelAdditive
open QuantitativeArithmeticTwoSequenceTaylor
open scoped MatrixGroups ModularForm

def realValue (w : Word) : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ (value w)
def coordA (w : Word) : ℝ := (realValue w).val 0 0
def coordB (w : Word) : ℝ := (realValue w).val 0 1
def coordC (w : Word) : ℝ := (realValue w).val 1 0
def coordD (w : Word) : ℝ := (realValue w).val 1 1

theorem realValue_det (w : Word) : (GeneralLinearGroup.det (realValue w):ℝ)=1 := by
  simp [realValue,SpecialLinearGroup.det_mapGL]
theorem coordinate_det (w : Word) : coordA w*coordD w-coordB w*coordC w=1 := by
  have h := realValue_det w
  change (realValue w).val.det=1 at h
  simpa only [Matrix.det_fin_two,coordA,coordB,coordC,coordD] using h

theorem original_word_fourier {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) (w : Word)
    (z : ℂ) (hz : 0<z.im) :
    fourier (fullCoefficients f (2*m)) z=
      1/(((coordC w:ℂ)*z+(coordD w:ℂ))^(2*m))*
        fourier (fullCoefficients f (2*m))
          (((coordA w:ℂ)*z+(coordB w:ℂ))/((coordC w:ℂ)*z+(coordD w:ℂ))) := by
  have hh : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] realValue w=
      SmallLevelOriginal.fourierFunction (2*m) f := original_words hf w
  have h := congrFun hh.symm ⟨z,hz⟩
  rw [det_one_slash _ (realValue_det w),zpow_neg,zpow_natCast] at h
  simp only [SmallLevelOriginal.fourierFunction] at h
  rw [coe_smul_of_det_pos (by rw [realValue_det]; norm_num)] at h
  simpa only [num,denom,coordA,coordB,coordC,coordD,one_div,
    mul_assoc,mul_comm,mul_left_comm] using h

/-- All-order Taylor--Fricke equations for every known level27 word,
with an analytic remainder derived from the original coefficient growth. -/
theorem original_word_taylor {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f)
    (w : Word) (hC : coordC w≠0) (j : ℝ) (hj : coordC w*j+coordD w≠0) :
    ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        transform (fullCoefficients f (2*m)) j s-
          (((coordC w*j+coordD w)^2:ℝ):ℂ)^(s-(m:ℂ))*
            (∑ n∈Finset.range M, (Complex.I*((coordC w*(coordC w*j+coordD w):ℝ):ℂ))^n*
              Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
              transform (fullCoefficients f (2*m))
                ((coordA w*j+coordB w)/(coordC w*j+coordD w)) (s+(n:ℂ)))=
          error M s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hF := original_word_fourier hf w
  have hh := matrix_even_rows (polynomial_bound hf.zero hg (2*m))
    (fullCoefficients_zero hf.zero (2*m)) m
    (coordA w) (coordB w) (coordC w) (coordD w) j hC
    (by rw [coordinate_det]; norm_num) hj 1 (by
      simpa only [coordinate_det,Complex.ofReal_one,one_pow,mul_one] using hF)
  simpa only [coordinate_det,div_one,one_mul] using hh
#print axioms original_word_fourier
#print axioms original_word_taylor
end QuantitativeArithmeticSmallLevelTwentySevenKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenEntireSourcesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenKnownWords
open Matrix UpperHalfPlane SmallLevelOriginal SmallLevelNormalized
open FinitenessOriginalInput QuantitativeArithmeticOriginalMatrixMellin
open scoped MatrixGroups ModularForm

theorem word_infinity_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : IsSolution 27 (2*m) f) (w : Word) (r : ℝ)
    (hC : coordC w≠0) (hr : coordC w*r+coordD w=0) :
    Differentiable ℂ (actualMellin (2*m) f r) := by
  apply source_entire (by omega : 0<2*m) hf (realValue w) (realValue_det w) 1
    (Or.inl rfl) _ r hC hr
  rw [one_smul]
  exact original_words hf w

/-- A known word sending a rational source to zero gives an entire Mellin
integral after composing with the original Fricke involution. -/
theorem word_zero_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : IsSolution 27 (2*m) f) (w : Word) (r : ℝ)
    (hA : coordA w≠0) (hr : coordA w*r+coordB w=0) :
    Differentiable ℂ (actualMellin (2*m) f r) := by
  obtain ⟨χ,hχ,hW⟩ := original_fricke_sign (by decide : 0<27) m hf
  let g : GL (Fin 2) ℝ := fricke 27 (by decide)*realValue w
  have hg : (GeneralLinearGroup.det g:ℝ)=1 := by
    have h1 := fricke_det 27 (by decide)
    have h2 := realValue_det w
    change (fricke 27 (by decide)).val.det=1 at h1
    change (realValue w).val.det=1 at h2
    change ((fricke 27 (by decide)).val*(realValue w).val).det=1
    rw [Matrix.det_mul,h1,h2,mul_one]
  have hs : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] g=χ • fourierFunction (2*m) f := by
    rw [show g=fricke 27 (by decide)*realValue w from rfl,SlashAction.slash_mul,hW,
      det_one_smul _ (realValue_det w)]
    have hw : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] realValue w=fourierFunction (2*m) f := original_words hf w
    rw [hw]
  have hc : g.val 1 0=Real.sqrt 27*coordA w := by
    norm_num [g,fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two,coordA]
  have hd : g.val 1 1=Real.sqrt 27*coordB w := by
    norm_num [g,fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two,coordB]
  apply source_entire (by omega : 0<2*m) hf g hg χ hχ hs r
  · rw [hc]
    exact mul_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)) hA
  · rw [hc,hd]
    linear_combination (Real.sqrt 27)*hr

#print axioms word_infinity_entire
#print axioms word_zero_entire
end QuantitativeArithmeticSmallLevelTwentySevenKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenSourceWordsDataV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenKnownWords
open Matrix
open scoped MatrixGroups
def sourceWord8 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.generator 1)) (Word.generator 1)) (Word.inv (Word.generator 0)))
def sourceWord9 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 1))) (Word.inv (Word.generator 1))) (Word.inv (Word.generator 1)))
def sourceWord10 : Word := (Word.mul (Word.mul Word.one (Word.inv (Word.generator 1))) (Word.inv (Word.generator 1)))
def sourceWord29 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 1))) (Word.inv (Word.generator 1))) (Word.generator 2))
def sourceWord33 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.generator 1)) (Word.generator 1)) (Word.generator 2))
def sourceWord41 : Word := (Word.mul (Word.mul Word.one (Word.inv (Word.generator 2))) (Word.inv (Word.generator 1)))
def sourceWord42 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.generator 1)) (Word.inv (Word.generator 2))) (Word.inv (Word.generator 1)))
def sourceWord49 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 1))) (Word.inv (Word.generator 2))) (Word.inv (Word.generator 0)))
def sourceWord50 : Word := (Word.mul (Word.mul Word.one (Word.inv (Word.generator 2))) (Word.inv (Word.generator 0)))
def sourceWord66 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 1))) (Word.generator 0)) (Word.generator 2))
def sourceWord70 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.generator 2)) (Word.generator 0)) (Word.inv (Word.generator 1)))
def sourceWord77 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 0))) (Word.generator 1)) (Word.inv (Word.generator 0)))
def sourceWord99 : Word := (Word.mul (Word.mul Word.one (Word.inv (Word.generator 0))) (Word.generator 2))
def sourceWord101 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.generator 0)) (Word.generator 1)) (Word.generator 2))
def sourceWord104 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.generator 1)) (Word.generator 2)) (Word.inv (Word.generator 1)))
def sourceWord106 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 0))) (Word.generator 2)) (Word.generator 0))
def sourceWord114 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 2))) (Word.inv (Word.generator 1))) (Word.inv (Word.generator 1)))
def sourceWord117 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 2))) (Word.generator 1)) (Word.inv (Word.generator 0)))
def sourceWord129 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 2))) (Word.inv (Word.generator 1))) (Word.generator 2))
def sourceWord130 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.generator 0)) (Word.generator 0)) (Word.inv (Word.generator 1)))
def sourceWord135 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 2))) (Word.generator 1)) (Word.generator 2))
def sourceWord139 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.generator 0)) (Word.generator 0)) (Word.generator 1))
def sourceWord142 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.generator 2)) (Word.inv (Word.generator 1))) (Word.inv (Word.generator 1)))
def sourceWord144 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.generator 0)) (Word.generator 0)) (Word.inv (Word.generator 2)))
def sourceWord145 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.generator 0)) (Word.inv (Word.generator 1))) (Word.generator 2))
def sourceWord151 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.generator 0)) (Word.inv (Word.generator 2))) (Word.generator 1))
def sourceWord154 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 2))) (Word.inv (Word.generator 2))) (Word.inv (Word.generator 1)))
def sourceWord156 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 2))) (Word.inv (Word.generator 2))) (Word.inv (Word.generator 0)))
def sourceWord172 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 2))) (Word.generator 0)) (Word.inv (Word.generator 1)))
def sourceWord179 : Word := (Word.mul (Word.mul (Word.mul Word.one (Word.inv (Word.generator 0))) (Word.generator 2)) (Word.generator 2))
end QuantitativeArithmeticSmallLevelTwentySevenKnownWords
end
end
