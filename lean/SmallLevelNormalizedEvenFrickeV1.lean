module

public import SmallLevelNormalizedFrickeV1
public import SmallLevelThirtySixOrbitV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelNormalized

open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem original_fricke_sign {N : ℕ} (hN : 0<N) (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke N hN=
        χ • SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨ε,hε,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  let χ : ℂ := ε*Complex.I^(2*m)
  have hχ : χ=1 ∨ χ= -1 := by
    have hi : Complex.I^(2*m)=(-1:ℂ)^m := by rw [pow_mul, Complex.I_sq]
    rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hε with rfl|rfl <;> simp [χ,hi,h]
  have h := fricke_law N (2*m) hN
    (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f (2*m))) χ (by
      intro z hz
      simpa [χ,FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
        Finset.sum_range_succ] using hlaw 1 (by decide) z hz)
  refine ⟨χ,hχ,?_⟩
  change SmallLevelOriginal.fourierFunction (2*m) f=χ •
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke N hN) at h
  rcases hχ with hc|hc
  · rw [hc] at h ⊢
    simpa using h.symm
  · rw [hc] at h ⊢
    simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg h.symm

/-- The central negative matrix acts trivially at even weight. -/
theorem central_even (g : ℍ → ℂ) (m : ℕ) :
    g ∣[((2*m:ℕ):ℤ)] (-1 : GL (Fin 2) ℝ)=g := by
  have h : SpecialLinearGroup.mapGL ℝ (-1 : SL(2,ℤ))=(-1 : GL (Fin 2) ℝ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe]
  rw [← h]
  exact SmallLevelThirtySix.slash_neg_one_even g m

#print axioms original_fricke_sign
#print axioms central_even

end SmallLevelNormalized
