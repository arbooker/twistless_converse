module

public import SmallLevelTwentyEightOriginalGeneratorsV1
public import QuantitativeArithmeticTwoSequenceTaylorTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightGrid
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct
open SmallLevelTwentyEightGenerators (E E_det W)
open scoped MatrixGroups ModularForm

/-- The five original generators used by the 84-grid continuation system. -/
def gridBase : Fin 5 → GL (Fin 2) ℝ
  | 0 => SpecialLinearGroup.mapGL ℝ T
  | 1 => SpecialLinearGroup.mapGL ℝ (lower 28)
  | 2 => E
  | 3 => W
  | 4 => translation (1/2)

def gridBaseSign (η : ℂ) : Fin 5 → ℂ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => η
  | 4 => -1

def gridLetter (i : Fin 5 × Bool) : GL (Fin 2) ℝ :=
  if i.2 then (gridBase i.1)⁻¹ else gridBase i.1

def gridWord : List (Fin 5 × Bool) → GL (Fin 2) ℝ
  | [] => 1
  | i::w => gridLetter i*gridWord w

def gridWordSign (η : ℂ) : List (Fin 5 × Bool) → ℂ
  | [] => 1
  | i::w => gridBaseSign η i.1*gridWordSign η w

theorem gridBase_det (i : Fin 5) : (GeneralLinearGroup.det (gridBase i):ℝ)=1 := by
  fin_cases i
  · change (SpecialLinearGroup.mapGL ℝ T).val.det=1
    norm_num [T,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,det_fin_two]
  · change (SpecialLinearGroup.mapGL ℝ (lower 28)).val.det=1
    norm_num [lower,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,det_fin_two]
  · exact E_det
  · exact fricke_det 28 (by decide)
  · exact translation_det (1/2)

theorem gridLetter_det (i : Fin 5 × Bool) : (GeneralLinearGroup.det (gridLetter i):ℝ)=1 := by
  simp only [gridLetter]
  split
  · exact det_one_inv _ (gridBase_det _)
  · exact gridBase_det _

theorem gridWord_det (w : List (Fin 5 × Bool)) : (GeneralLinearGroup.det (gridWord w):ℝ)=1 := by
  induction w with
  | nil => simp [gridWord]
  | cons i w ih => simp only [gridWord,map_mul,Units.val_mul,gridLetter_det,ih,one_mul]

theorem gridBaseSign_unit {η : ℂ} (hη : η=1 ∨ η= -1)
    (i : Fin 5) : gridBaseSign η i=1 ∨ gridBaseSign η i= -1 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact hη
  · exact Or.inr rfl

theorem gridWordSign_unit {η : ℂ} (hη : η=1 ∨ η= -1)
    (w : List (Fin 5 × Bool)) : gridWordSign η w=1 ∨ gridWordSign η w= -1 := by
  induction w with
  | nil => exact Or.inl rfl
  | cons i w ih =>
    rcases gridBaseSign_unit hη i.1 with hi|hi <;> rcases ih with hw|hw <;>
      simp [gridWordSign,hi,hw]

private theorem eigen_inv {k : ℤ} {F : ℍ→ℂ} {g : GL (Fin 2) ℝ}
    (hg : (GeneralLinearGroup.det g:ℝ)=1) {χ : ℂ} (hχ : χ=1 ∨ χ= -1)
    (h : F ∣[k] g=χ • F) : F ∣[k] g⁻¹=χ • F := by
  have hh:=congrArg (fun H : ℍ→ℂ => H ∣[k] g⁻¹) h
  rw [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one,
    det_one_smul _ (det_one_inv _ hg)] at hh
  rcases hχ with rfl|rfl
  · simpa using hh.symm
  · simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg hh.symm

/-- Word laws with a specified coherent Fricke sign. This version allows
the same original sign to be used in the Ramanujan and matrix Taylor rows. -/
theorem grid_words_of_fricke (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 28 (2*m) f)
    {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f) :
    ∀ w : List (Fin 5 × Bool),
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] gridWord w=
        gridWordSign η w • SmallLevelOriginal.fourierFunction (2*m) f := by
  have hb (i : Fin 5) : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] gridBase i=
      gridBaseSign η i • SmallLevelOriginal.fourierFunction (2*m) f := by
    fin_cases i
    · change _=1 • _
      rw [one_smul]
      exact original_T (2*m) f
    · change _=1 • _
      rw [one_smul]
      exact original_lower (by decide : 0<28) hf
    · simpa only [gridBase,gridBaseSign,one_smul] using (SmallLevelTwentyEightGenerators.original_generators m hf η hη hW).2
    · exact hW
    · simpa only [gridBase,gridBaseSign,neg_one_smul] using SmallLevelEvenScale.original_half_translation (L:=7) hf.toEulerData (2*m)
  have hl (i : Fin 5 × Bool) : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] gridLetter i=
      gridBaseSign η i.1 • SmallLevelOriginal.fourierFunction (2*m) f := by
    simp only [gridLetter]
    split
    · exact eigen_inv (gridBase_det _) (gridBaseSign_unit hη _) (hb _)
    · exact hb _
  intro w
  induction w with
  | nil => simp [gridWord,gridWordSign]
  | cons i w ih =>
    rw [gridWord,gridWordSign,SlashAction.slash_mul,hl,
      det_one_smul _ (gridWord_det _),ih,smul_smul]

/-- One coherent original Fricke sign gives all signed word laws. -/
theorem original_grid_words (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 28 (2*m) f) :
    ∃ η : ℂ, (η=1 ∨ η= -1) ∧ ∀ w : List (Fin 5 × Bool),
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] gridWord w=
        gridWordSign η w • SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨η,hη,hW⟩:=original_fricke_sign (by decide : 0<28) m hf
  exact ⟨η,hη,grid_words_of_fricke m hf hη hW⟩

/-- A signed determinant-one word law is the literal Fourier law needed by
matrix Taylor expansion; the sign is its own inverse. -/
theorem grid_word_fourier {m : ℕ} {f : ℕ→ℂ} {w : List (Fin 5 × Bool)}
    {χ : ℂ} (hχ : χ=1 ∨ χ= -1)
    (h : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] gridWord w=
      χ • SmallLevelOriginal.fourierFunction (2*m) f)
    (z : ℂ) (hz : 0<z.im) :
    fourier (fullCoefficients f (2*m)) z=
      χ/(((gridWord w).val 1 0:ℂ)*z+((gridWord w).val 1 1:ℂ))^(2*m)*
        fourier (fullCoefficients f (2*m))
          ((((gridWord w).val 0 0:ℂ)*z+((gridWord w).val 0 1:ℂ))/
            (((gridWord w).val 1 0:ℂ)*z+((gridWord w).val 1 1:ℂ))) := by
  have hback : SmallLevelOriginal.fourierFunction (2*m) f=
      χ • (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] gridWord w) := by
    rcases hχ with rfl|rfl
    · simpa using h.symm
    · simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg h.symm
  have hh:=congrFun hback ⟨z,hz⟩
  rw [Pi.smul_apply,smul_eq_mul,det_one_slash _ (gridWord_det _),zpow_neg,zpow_natCast] at hh
  simp only [SmallLevelOriginal.fourierFunction] at hh
  rw [coe_smul_of_det_pos (by rw [gridWord_det]; norm_num)] at hh
  simpa only [num,denom,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

#print axioms grid_words_of_fricke
#print axioms original_grid_words
#print axioms grid_word_fourier
end SmallLevelTwentyEightGrid
