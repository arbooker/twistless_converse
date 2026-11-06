module

public import SmallLevelSixRootsV1
public import SmallLevelOddFrickeV1
public import SmallLevelNormalizedEvenFrickeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

/-- The five transformations used by the augmented level-33 pole system. -/
def seed : Fin 5 → GL (Fin 2) ℝ
  | 0 => SpecialLinearGroup.mapGL ℝ T
  | 1 => SpecialLinearGroup.mapGL ℝ (lower 33)
  | 2 => SpecialLinearGroup.mapGL ℝ ((oddMatrix 33 17 (by decide))⁻¹)
  | 3 => fricke 33 (by decide)
  | _ => SmallLevelThirtyThree.B

def seedSign (χ δ : ℂ) (i : Fin 5) : ℂ := if i=3 then χ else if i=4 then δ else 1

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

def character (χ δ : ℂ) : Word → ℂ
  | .one => 1
  | .generator i => seedSign χ δ i
  | .mul u v => character χ δ u*character χ δ v
  | .inv w => character χ δ w

theorem seed_det (i : Fin 5) : (GeneralLinearGroup.det (seed i):ℝ)=1 := by
  fin_cases i
  · simp [seed,SpecialLinearGroup.det_mapGL]
  · simp [seed,SpecialLinearGroup.det_mapGL]
  · simp [seed,SpecialLinearGroup.det_mapGL]
  · exact fricke_det 33 (by decide)
  · exact SmallLevelThirtyThree.B_det

theorem value_det (w : Word) : (GeneralLinearGroup.det (value w):ℝ)=1 := by
  induction w with
  | one => simp [value]
  | generator i => exact seed_det i
  | mul u v hu hv => simpa [value] using congrArg₂ (fun a b : ℝ => a*b) hu hv
  | inv w hw => exact det_one_inv _ hw

theorem character_sign {χ δ : ℂ} (hχ : χ=1 ∨ χ= -1) (hδ : δ=1 ∨ δ= -1) (w : Word) :
    character χ δ w=1 ∨ character χ δ w= -1 := by
  induction w with
  | one => exact Or.inl rfl
  | generator i =>
    by_cases hi : i=3
    · simpa only [character,seedSign,ite_eq_left hi] using hχ
    · by_cases hj : i=4
      · simpa only [character,seedSign,ite_eq_right hi,ite_eq_left hj] using hδ
      · exact Or.inl (by simp [character,seedSign,hi,hj])
  | mul u v hu hv =>
    rcases hu with hu|hu <;> rcases hv with hv|hv <;> simp [character,hu,hv]
  | inv w hw => exact hw

theorem original_seeds {m : ℕ} (hm : 0 < m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ i : Fin 5,
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] seed i=
        seedSign χ (FinitenessNormalizedTwistProduct.root 33 f 3) i • SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨χ,hχ,hF⟩ := original_fricke_sign (by decide : 0<33) m hf
  refine ⟨χ,hχ,?_⟩
  intro i
  let K := slashStabilizer ((2*m:ℕ):ℤ) (SmallLevelOriginal.fourierFunction (2*m) f)
  have ho : (oddMatrix 33 17 (by decide))⁻¹∈K := K.inv_mem
    (original_odd (by decide) (by decide : 2*17=33+1) (by decide) hf)
  fin_cases i
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] T=1 • _
    simpa only [one_smul] using original_T (2*m) f
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] lower 33=1 • _
    simpa only [one_smul] using original_lower (by decide : 0<33) hf
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      (oddMatrix 33 17 (by decide))⁻¹=1 • _
    rw [one_smul]
    exact ho
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      fricke 33 (by decide)=χ • _
    exact hF
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SmallLevelThirtyThree.B=
      FinitenessNormalizedTwistProduct.root 33 f 3 • _
    exact SmallLevelSixEigen.thirty_three_B (by omega) hf

/-- Every finite word in the known generators and their inverses has its
actual slash eigenrelation, with one coherent original Fricke sign. -/
theorem original_words {m : ℕ} (hm : 0 < m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ w : Word,
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] value w=
        character χ (FinitenessNormalizedTwistProduct.root 33 f 3) w • SmallLevelOriginal.fourierFunction (2*m) f := by
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
    change _ ∣[((2*m:ℕ):ℤ)] (value w)⁻¹=character χ (FinitenessNormalizedTwistProduct.root 33 f 3) w • _
    rcases character_sign hχ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3) w with hc|hc
    · simpa only [hc,one_smul] using hh.symm
    · simpa only [hc,neg_one_smul,neg_neg] using congrArg Neg.neg hh.symm

#print axioms seed_det
#print axioms value_det
#print axioms character_sign
#print axioms original_seeds
#print axioms original_words
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
