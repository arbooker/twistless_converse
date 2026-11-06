module

public import QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRowsTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
open scoped MatrixGroups ModularForm

/-- The five transformations used to generate the complete level35 rows. -/
def seed : Fin 5 → GL (Fin 2) ℝ
  | 0 => SpecialLinearGroup.mapGL ℝ T
  | 1 => SpecialLinearGroup.mapGL ℝ (lower 35)
  | 2 => SpecialLinearGroup.mapGL ℝ ((oddMatrix 35 18 (by decide))⁻¹)
  | 3 => SpecialLinearGroup.mapGL ℝ six
  | _ => fricke 35 (by decide)

def seedSign (χ : ℂ) (i : Fin 5) : ℂ := if i=4 then χ else 1

inductive Word where
  | one : Word
  | generator : Fin 5 → Word
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

theorem seed_det (i : Fin 5) : (GeneralLinearGroup.det (seed i):ℝ)=1 := by
  fin_cases i
  · simp [seed,SpecialLinearGroup.det_mapGL]
  · simp [seed,SpecialLinearGroup.det_mapGL]
  · simp [seed,SpecialLinearGroup.det_mapGL]
  · simp [seed,SpecialLinearGroup.det_mapGL]
  · exact fricke_det 35 (by decide)

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
    by_cases hi : i=4
    · simpa only [character,seedSign,ite_eq_left hi] using hχ
    · exact Or.inl (by simp [character,seedSign,hi])
  | mul u v hu hv =>
    rcases hu with hu|hu <;> rcases hv with hv|hv <;> simp [character,hu,hv]
  | inv w hw => exact hw

theorem original_seeds {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ i : Fin 5,
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] seed i=
        seedSign χ i • SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨χ,hχ,hF⟩ := original_fricke_sign (by decide : 0<35) m hf
  refine ⟨χ,hχ,?_⟩
  intro i
  let K := slashStabilizer ((2*m:ℕ):ℤ) (SmallLevelOriginal.fourierFunction (2*m) f)
  have ho : (oddMatrix 35 18 (by decide))⁻¹∈K := K.inv_mem
    (original_odd (by decide) (by decide : 2*18=35+1) (by decide) hf)
  fin_cases i
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] T=1 • _
    simpa only [one_smul] using original_T (2*m) f
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] lower 35=1 • _
    simpa only [one_smul] using original_lower (by decide : 0<35) hf
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      (oddMatrix 35 18 (by decide))⁻¹=1 • _
    rw [one_smul]
    exact ho
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] six=1 • _
    simpa only [one_smul] using original_six (by omega : 0<2*m) hf
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      fricke 35 (by decide)=χ • _
    exact hF

/-- Every finite word in the known generators and their inverses has its
actual slash eigenrelation, with one coherent original Fricke sign. -/
theorem original_words {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ w : Word,
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] value w=
        character χ w • SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨χ,hχ,hseed⟩ := original_seeds hm hf
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
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
