module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import QuantitativeArithmeticCoherentTaylorTheoryV4
public import QuantitativeArithmeticTwoSequenceTaylorTheoryV4
public import SmallLevelNormalizedEvenFrickeV1
public import SmallLevelOddFrickeV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFiveKnownWords. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveKnownWordsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

/-- The four transformations used by the augmented level-25 pole system. -/
def seed : Fin 4 → GL (Fin 2) ℝ
  | 0 => SpecialLinearGroup.mapGL ℝ T
  | 1 => SpecialLinearGroup.mapGL ℝ (lower 25)
  | 2 => SpecialLinearGroup.mapGL ℝ ((oddMatrix 25 13 (by decide))⁻¹)
  | _ => fricke 25 (by decide)

def seedSign (χ : ℂ) (i : Fin 4) : ℂ := if i=3 then χ else 1

inductive Word where
  | one : Word
  | generator : Fin 4 → Word
  | mul : Word → Word → Word
  | inv : Word → Word

def value : Word → GL (Fin 2) ℝ
  | .one => 1
  | .generator i => seed i
  | .mul u v => value u*value v
  | .inv w => (value w)⁻¹

def character (χ : ℂ) : Word → ℂ
  | .one => 1
  | .generator i => seedSign χ i
  | .mul u v => character χ u*character χ v
  | .inv w => character χ w

theorem seed_det (i : Fin 4) : (GeneralLinearGroup.det (seed i):ℝ)=1 := by
  fin_cases i
  · simp [seed,SpecialLinearGroup.det_mapGL]
  · simp [seed,SpecialLinearGroup.det_mapGL]
  · simp [seed,SpecialLinearGroup.det_mapGL]
  · exact fricke_det 25 (by decide)

theorem value_det (w : Word) : (GeneralLinearGroup.det (value w):ℝ)=1 := by
  induction w with
  | one => simp [value]
  | generator i => exact seed_det i
  | mul u v hu hv => simpa [value] using congrArg₂ (fun a b : ℝ => a*b) hu hv
  | inv w hw => exact det_one_inv _ hw

theorem character_sign {χ : ℂ} (hχ : χ=1 ∨ χ= -1) (w : Word) :
    character χ w=1 ∨ character χ w= -1 := by
  induction w with
  | one => exact Or.inl rfl
  | generator i =>
    by_cases hi : i=3
    · simpa only [character,seedSign,ite_eq_left hi] using hχ
    · exact Or.inl (by simp [character,seedSign,hi])
  | mul u v hu hv =>
    rcases hu with hu|hu <;> rcases hv with hv|hv <;> simp [character,hu,hv]
  | inv w hw => exact hw

theorem original_seeds {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ i : Fin 4,
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] seed i=
        seedSign χ i • SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨χ,hχ,hF⟩ := original_fricke_sign (by decide : 0<25) m hf
  refine ⟨χ,hχ,?_⟩
  intro i
  let K := slashStabilizer ((2*m:ℕ):ℤ) (SmallLevelOriginal.fourierFunction (2*m) f)
  have ho : (oddMatrix 25 13 (by decide))⁻¹∈K := K.inv_mem
    (original_odd (by decide) (by decide : 2*13=25+1) (by decide) hf)
  fin_cases i
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] T=1 • _
    simpa only [one_smul] using original_T (2*m) f
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] lower 25=1 • _
    simpa only [one_smul] using original_lower (by decide : 0<25) hf
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      (oddMatrix 25 13 (by decide))⁻¹=1 • _
    rw [one_smul]
    exact ho
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      fricke 25 (by decide)=χ • _
    exact hF

/-- Every finite word in the known generators and their inverses has its
actual slash eigenrelation, with one coherent original Fricke sign. -/
theorem original_words {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ w : Word,
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] value w=
        character χ w • SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨χ,hχ,hseed⟩ := original_seeds hf
  refine ⟨χ,hχ,?_⟩
  intro w
  induction w with
  | one => simp [value,character,SlashAction.slash_one]
  | generator i => exact hseed i
  | mul u v hu hv =>
    rw [value,character,SlashAction.slash_mul,hu,det_one_smul _ (value_det v),hv,mul_smul]
  | inv w hw =>
    have hh := congrArg (fun H : ℍ → ℂ => H ∣[((2*m:ℕ):ℤ)] (value w)⁻¹) hw
    rw [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one,
      det_one_smul _ (det_one_inv _ (value_det w))] at hh
    change _ ∣[((2*m:ℕ):ℤ)] (value w)⁻¹=character χ w • _
    rcases character_sign hχ w with hc|hc
    · simpa only [hc,one_smul] using hh.symm
    · simpa only [hc,neg_one_smul,neg_neg] using congrArg Neg.neg hh.symm

#print axioms seed_det
#print axioms value_det
#print axioms character_sign
#print axioms original_seeds
#print axioms original_words
end QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveKnownWordFourierV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
open Matrix UpperHalfPlane SmallLevelNormalized Complex Set
open FinitenessOriginalFourier FinitenessFourierConstruction SmallLevelAdditive
open QuantitativeArithmeticTwoSequenceTaylor
open scoped MatrixGroups ModularForm

def coordA (w : Word) : ℝ := (value w).val 0 0
def coordB (w : Word) : ℝ := (value w).val 0 1
def coordC (w : Word) : ℝ := (value w).val 1 0
def coordD (w : Word) : ℝ := (value w).val 1 1

theorem coordinate_det (w : Word) : coordA w*coordD w-coordB w*coordC w=1 := by
  have h := value_det w
  change (value w).val.det=1 at h
  simpa only [Matrix.det_fin_two,coordA,coordB,coordC,coordD] using h

theorem word_fourier_of_slash (m : ℕ) (f : ℕ → ℂ) (χ : ℂ)
    (hχ : χ=1 ∨ χ= -1) (w : Word)
    (hw : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] value w=
      character χ w • SmallLevelOriginal.fourierFunction (2*m) f)
    (z : ℂ) (hz : 0<z.im) :
    fourier (fullCoefficients f (2*m)) z=
      character χ w/(((coordC w:ℂ)*z+(coordD w:ℂ))^(2*m))*
        fourier (fullCoefficients f (2*m))
          (((coordA w:ℂ)*z+(coordB w:ℂ))/((coordC w:ℂ)*z+(coordD w:ℂ))) := by
  have hback : SmallLevelOriginal.fourierFunction (2*m) f=
      character χ w • (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] value w) := by
    rcases character_sign hχ w with hc|hc
    · simpa only [hc,one_smul] using hw.symm
    · simpa only [hc,neg_one_smul,neg_neg] using congrArg Neg.neg hw.symm
  have h := congrFun hback ⟨z,hz⟩
  rw [Pi.smul_apply,smul_eq_mul,det_one_slash _ (value_det w),zpow_neg,zpow_natCast] at h
  simp only [SmallLevelOriginal.fourierFunction] at h
  rw [coe_smul_of_det_pos (by rw [value_det]; norm_num)] at h
  simpa only [num,denom,coordA,coordB,coordC,coordD,div_eq_mul_inv,
    mul_assoc,mul_comm,mul_left_comm] using h

/-- Actual all-order Fourier/Taylor laws for every word used in the complete
row construction. The hypotheses on C and the source only exclude an affine
row or a source sent to infinity, which are treated separately. -/
theorem original_word_taylor {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ w : Word, coordC w≠0 →
      ∀ j : ℝ, coordC w*j+coordD w≠0 →
      ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
        AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, bound<s.re →
          transform (fullCoefficients f (2*m)) j s-
            character χ w*(((coordC w*j+coordD w)^2:ℝ):ℂ)^(s-(m:ℂ))*
              (∑ n∈Finset.range M, (Complex.I*((coordC w*(coordC w*j+coordD w):ℝ):ℂ))^n*
                Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
                transform (fullCoefficients f (2*m))
                  ((coordA w*j+coordB w)/(coordC w*j+coordD w)) (s+(n:ℂ)))=
            error M s := by
  obtain ⟨χ,hχ,hwords⟩ := original_words hf
  refine ⟨χ,hχ,?_⟩
  intro w hC j hj
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hF := word_fourier_of_slash m f χ hχ w (hwords w)
  have hh := matrix_even_rows (polynomial_bound hf.zero hg (2*m))
    (fullCoefficients_zero hf.zero (2*m)) m
    (coordA w) (coordB w) (coordC w) (coordD w) j hC
    (by rw [coordinate_det]; norm_num) hj (character χ w) (by
      simpa only [coordinate_det,Complex.ofReal_one,one_pow,mul_one] using hF)
  simpa only [coordinate_det,div_one] using hh

#print axioms coordinate_det
#print axioms word_fourier_of_slash
#print axioms original_word_taylor
end QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveCoherentWordsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem seeds_of_fricke {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) (χ : ℂ)
    (hF : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      fricke 25 (by decide)=χ • SmallLevelOriginal.fourierFunction (2*m) f) :
    ∀ i : Fin 4,
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] seed i=
        seedSign χ i • SmallLevelOriginal.fourierFunction (2*m) f := by
  intro i
  let K := slashStabilizer ((2*m:ℕ):ℤ) (SmallLevelOriginal.fourierFunction (2*m) f)
  have ho : (oddMatrix 25 13 (by decide))⁻¹∈K := K.inv_mem
    (original_odd (by decide) (by decide : 2*13=25+1) (by decide) hf)
  fin_cases i
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] T=1 • _
    simpa only [one_smul] using original_T (2*m) f
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] lower 25=1 • _
    simpa only [one_smul] using original_lower (by decide : 0<25) hf
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      (oddMatrix 25 13 (by decide))⁻¹=1 • _
    rw [one_smul]
    exact ho
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      fricke 25 (by decide)=χ • _
    exact hF

/-- Every finite word in the known generators and their inverses has its
actual slash eigenrelation, with one coherent original Fricke sign. -/
theorem words_of_fricke {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) (χ : ℂ)
    (hχ : χ=1 ∨ χ= -1)
    (hF : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      fricke 25 (by decide)=χ • SmallLevelOriginal.fourierFunction (2*m) f) :
    ∀ w : Word,
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] value w=
        character χ w • SmallLevelOriginal.fourierFunction (2*m) f := by
  have hseed := seeds_of_fricke hf χ hF
  intro w
  induction w with
  | one => simp [value,character,SlashAction.slash_one]
  | generator i => exact hseed i
  | mul u v hu hv =>
    rw [value,character,SlashAction.slash_mul,hu,det_one_smul _ (value_det v),hv,mul_smul]
  | inv w hw =>
    have hh := congrArg (fun H : ℍ → ℂ => H ∣[((2*m:ℕ):ℤ)] (value w)⁻¹) hw
    rw [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one,
      det_one_smul _ (det_one_inv _ (value_det w))] at hh
    change _ ∣[((2*m:ℕ):ℤ)] (value w)⁻¹=character χ w • _
    rcases character_sign hχ w with hc|hc
    · simpa only [hc,one_smul] using hh.symm
    · simpa only [hc,neg_one_smul,neg_neg] using congrArg Neg.neg hh.symm

/-- One original sign supplies both every Ramanujan transformation law and
all known group-word transformations. -/
theorem original_coherent_word_laws {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε ∧
      (ε*Complex.I^(2*m)=1 ∨ ε*Complex.I^(2*m)= -1) ∧
      ∀ w : Word,
        SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] value w=
          character (ε*Complex.I^(2*m)) w • SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨ε,hε,hlaw⟩ := QuantitativeArithmeticCoherentTaylor.original_coherent_law
    (by decide : 0<25) hf
  obtain ⟨hχ,hF⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<25) m ε hε hlaw
  exact ⟨ε,hε,hlaw,hχ,words_of_fricke hf _ hχ hF⟩

#print axioms seeds_of_fricke
#print axioms words_of_fricke
#print axioms original_coherent_word_laws
end QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveCoherentWordTaylorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
open Matrix UpperHalfPlane SmallLevelNormalized Complex Set
open FinitenessOriginalFourier FinitenessFourierConstruction SmallLevelAdditive
open QuantitativeArithmeticTwoSequenceTaylor
open scoped MatrixGroups ModularForm

/-- Actual all-order Fourier/Taylor laws for every word used in the complete
row construction. The hypotheses on C and the source only exclude an affine
row or a source sent to infinity, which are treated separately. -/
theorem word_taylor_of_law {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε) :
    ∀ w : Word, coordC w≠0 →
      ∀ j : ℝ, coordC w*j+coordD w≠0 →
      ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
        AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, bound<s.re →
          transform (fullCoefficients f (2*m)) j s-
            character (ε*Complex.I^(2*m)) w*(((coordC w*j+coordD w)^2:ℝ):ℂ)^(s-(m:ℂ))*
              (∑ n∈Finset.range M, (Complex.I*((coordC w*(coordC w*j+coordD w):ℝ):ℂ))^n*
                Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
                transform (fullCoefficients f (2*m))
                  ((coordA w*j+coordB w)/(coordC w*j+coordD w)) (s+(n:ℂ)))=
            error M s := by
  obtain ⟨hχ,hfricke⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<25) m ε hε hlaw
  have hwords := words_of_fricke hf (ε*Complex.I^(2*m)) hχ hfricke
  intro w hC j hj
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hF := word_fourier_of_slash m f (ε*Complex.I^(2*m)) hχ w (hwords w)
  have hh := matrix_even_rows (polynomial_bound hf.zero hg (2*m))
    (fullCoefficients_zero hf.zero (2*m)) m
    (coordA w) (coordB w) (coordC w) (coordD w) j hC
    (by rw [coordinate_det]; norm_num) hj (character (ε*Complex.I^(2*m)) w) (by
      simpa only [coordinate_det,Complex.ofReal_one,one_pow,mul_one] using hF)
  simpa only [coordinate_det,div_one] using hh

#print axioms word_taylor_of_law
end QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveRawWordsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
open Matrix SmallLevelNormalized
open scoped MatrixGroups

/-- Integral seed representatives; the Fricke representative has determinant21. -/
def rawSeed (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℝ :=
  if i=3 then !![0,-1;25,0] else (seed i).val

def seedScale (i : Fin 4) : ℝ := if i=3 then (Real.sqrt 25)⁻¹ else 1

/-- Adjugation represents projective inversion without introducing any
rational denominators. -/
def raw : Word → Matrix (Fin 2) (Fin 2) ℝ
  | .one => 1
  | .generator i => rawSeed i
  | .mul u v => raw u*raw v
  | .inv w => (raw w).adjugate

def wordScale : Word → ℝ
  | .one => 1
  | .generator i => seedScale i
  | .mul u v => wordScale u*wordScale v
  | .inv w => wordScale w

theorem seedScale_pos (i : Fin 4) : 0<seedScale i := by
  unfold seedScale
  split
  · exact inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  · norm_num

theorem wordScale_pos (w : Word) : 0<wordScale w := by
  induction w with
  | one => norm_num [wordScale]
  | generator i => exact seedScale_pos i
  | mul u v hu hv => exact mul_pos hu hv
  | inv w hw => exact hw

theorem seed_raw (i : Fin 4) : (seed i).val=seedScale i • rawSeed i := by
  by_cases hi : i=3
  · subst i
    have hs : (Real.sqrt (25:ℝ))^2=25 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt (25:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [seed,seedScale,rawSeed,fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
        Matrix.smul_apply,smul_eq_mul]
    · simp only [div_eq_mul_inv,neg_mul,one_mul]
    · calc
        Real.sqrt 25 = (Real.sqrt 25)⁻¹*(Real.sqrt 25*Real.sqrt 25) := by
          rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]
        _ = (Real.sqrt 25)⁻¹*25 := by rw [← pow_two,hs]
  · simp [seedScale,rawSeed,hi]

theorem inverse_val_adjugate (g : GL (Fin 2) ℝ)
    (hg : (GeneralLinearGroup.det g:ℝ)=1) : g⁻¹.val=g.val.adjugate := by
  have hdet : g.val.det=1 := hg
  have ha : g.val*g.val.adjugate=1 := by
    rw [Matrix.mul_adjugate,hdet,one_smul]
  calc
    g⁻¹.val = g⁻¹.val*1 := by rw [Matrix.mul_one]
    _ = g⁻¹.val*(g.val*g.val.adjugate) := by rw [ha]
    _ = g.val.adjugate := by rw [← Matrix.mul_assoc,Units.inv_mul,Matrix.one_mul]

/-- Actual normalized matrix values equal positive scalars times the
integer projective representatives, for arbitrary words and inverses. -/
theorem value_raw (w : Word) : (value w).val=wordScale w • raw w := by
  induction w with
  | one => simp [value,wordScale,raw]
  | generator i => exact seed_raw i
  | mul u v hu hv =>
    change (value u).val*(value v).val=(wordScale u*wordScale v) • (raw u*raw v)
    rw [hu,hv,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  | inv w hw =>
    change (value w)⁻¹.val=wordScale w • (raw w).adjugate
    rw [inverse_val_adjugate _ (value_det w),hw,Matrix.adjugate_smul]
    simp

theorem raw_det_scale (w : Word) : (wordScale w)^2*(raw w).det=1 := by
  have hd : (value w).val.det=1 := value_det w
  rw [value_raw,Matrix.det_smul] at hd
  simpa using hd

theorem raw_det_pos (w : Word) : 0<(raw w).det := by
  have hs := sq_pos_of_pos (wordScale_pos w)
  have hd := raw_det_scale w
  nlinarith

#print axioms seed_raw
#print axioms inverse_val_adjugate
#print axioms value_raw
#print axioms raw_det_scale
#print axioms raw_det_pos
end QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveRawWordCoordinatesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
open Matrix Complex

def rawA (w : Word) : ℝ := raw w 0 0
def rawB (w : Word) : ℝ := raw w 0 1
def rawC (w : Word) : ℝ := raw w 1 0
def rawD (w : Word) : ℝ := raw w 1 1
theorem raw_det_formula (w : Word) : (raw w).det=rawA w*rawD w-rawB w*rawC w := by
  simp only [Matrix.det_fin_two,rawA,rawB,rawC,rawD]

theorem raw_coordinates (w : Word) :
    coordA w=wordScale w*rawA w ∧ coordB w=wordScale w*rawB w ∧
    coordC w=wordScale w*rawC w ∧ coordD w=wordScale w*rawD w := by
  have hh (i j : Fin 2) := congrFun (congrFun (value_raw w) i) j
  exact ⟨hh 0 0,hh 0 1,hh 1 0,hh 1 1⟩

theorem raw_C_ne_zero (w : Word) : coordC w≠0 ↔ rawC w≠0 := by
  rw [(raw_coordinates w).2.2.1,mul_ne_zero_iff]
  exact and_iff_right (wordScale_pos w).ne'


#print axioms raw_coordinates
end QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveIntegerWordsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
open Matrix SmallLevelNormalized SmallLevelGenerators ModularGroup
open scoped MatrixGroups

def integerSeed : Fin 4 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![1,1;0,1]
  | 1 => !![1,0;25,1]
  | 2 => !![2,-1;-25,13]
  | _ => !![0,-1;25,0]

def integerRaw : Word → Matrix (Fin 2) (Fin 2) ℤ
  | .one => 1
  | .generator i => integerSeed i
  | .mul u v => integerRaw u*integerRaw v
  | .inv w => (integerRaw w).adjugate

theorem rawSeed_integer (i : Fin 4) : rawSeed i=(integerSeed i).map (Int.castRingHom ℝ) := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [rawSeed,integerSeed,seed,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe,SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.inv_def,Matrix.det_fin_two,SmallLevelGenerators.oddMatrix,SmallLevelGenerators.lower,
      ModularGroup.T,Matrix.map_apply]

/-- The integer word calculation is an exact representative of the analytic
matrix, including inverse words. -/
theorem raw_integer (w : Word) : raw w=(integerRaw w).map (Int.castRingHom ℝ) := by
  induction w with
  | one => simp [raw,integerRaw]
  | generator i => exact rawSeed_integer i
  | mul u v hu hv =>
    simp only [raw,integerRaw,hu,hv]
    ext i j
    simp [Matrix.mul_apply,Fin.sum_univ_two]
  | inv w hw =>
    simp only [raw,integerRaw,hw]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.adjugate_fin_two,Matrix.map_apply]

/-- Character bookkeeping is just the parity of the Fricke letters. -/
def frickeCount : Word → ℕ
  | .one => 0
  | .generator i => if i=3 then 1 else 0
  | .mul u v => frickeCount u+frickeCount v
  | .inv w => frickeCount w

theorem character_count (χ : ℂ) (w : Word) : character χ w=χ^(frickeCount w) := by
  induction w with
  | one => simp [character,frickeCount]
  | generator i => by_cases hi : i=3 <;> simp [character,seedSign,frickeCount,hi]
  | mul u v hu hv => simp only [character,frickeCount,pow_add,hu,hv]
  | inv w hw => exact hw

#print axioms rawSeed_integer
#print axioms raw_integer
#print axioms character_count
end QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveIntegerWordAlgebraV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
open Matrix Complex

theorem raw_det_integer (w : Word) : (raw w).det=((integerRaw w).det : ℝ) := by
  rw [raw_integer]
  simp [Matrix.det_fin_two,Matrix.map_apply]

theorem integer_det_pos (w : Word) : 0<(integerRaw w).det := by
  have hp := raw_det_pos w
  rw [raw_det_integer] at hp
  exact_mod_cast hp

theorem word_C_integer (w : Word) : coordC w≠0 ↔ integerRaw w 1 0≠0 := by
  rw [raw_C_ne_zero]
  simp [rawC,raw_integer,Matrix.map_apply]


#print axioms word_C_integer
end QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
end
end
