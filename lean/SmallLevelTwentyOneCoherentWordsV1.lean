module

public import SmallLevelTwentyOneKnownWordFourierV1
public import QuantitativeArithmeticCoherentTaylorTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace SmallLevelTwentyOneKnownWords
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem seeds_of_fricke {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (χ : ℂ)
    (hF : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      fricke 21 (by decide)=χ • SmallLevelOriginal.fourierFunction (2*m) f) :
    ∀ i : Fin 4,
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] seed i=
        seedSign χ i • SmallLevelOriginal.fourierFunction (2*m) f := by
  intro i
  let K := slashStabilizer ((2*m:ℕ):ℤ) (SmallLevelOriginal.fourierFunction (2*m) f)
  have ho : (oddMatrix 21 11 (by decide))⁻¹∈K := K.inv_mem
    (original_odd (by decide) (by decide : 2*11=21+1) (by decide) hf)
  fin_cases i
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] T=1 • _
    simpa only [one_smul] using original_T (2*m) f
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] lower 21=1 • _
    simpa only [one_smul] using original_lower (by decide : 0<21) hf
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      (oddMatrix 21 11 (by decide))⁻¹=1 • _
    rw [one_smul]
    exact ho
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      fricke 21 (by decide)=χ • _
    exact hF

/-- Every finite word in the known generators and their inverses has its
actual slash eigenrelation, with one coherent original Fricke sign. -/
theorem words_of_fricke {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (χ : ℂ)
    (hχ : χ=1 ∨ χ= -1)
    (hF : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      fricke 21 (by decide)=χ • SmallLevelOriginal.fourierFunction (2*m) f) :
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
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε ∧
      (ε*Complex.I^(2*m)=1 ∨ ε*Complex.I^(2*m)= -1) ∧
      ∀ w : Word,
        SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] value w=
          character (ε*Complex.I^(2*m)) w • SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨ε,hε,hlaw⟩ := QuantitativeArithmeticCoherentTaylor.original_coherent_law
    (by decide : 0<21) hf
  obtain ⟨hχ,hF⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<21) m ε hε hlaw
  exact ⟨ε,hε,hlaw,hχ,words_of_fricke hf _ hχ hF⟩

#print axioms seeds_of_fricke
#print axioms words_of_fricke
#print axioms original_coherent_word_laws
end SmallLevelTwentyOneKnownWords
