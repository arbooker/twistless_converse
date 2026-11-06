module
public import QuantitativeArithmeticSmallLevelThirtyThreeCoherentWordsV1
public import QuantitativeArithmeticMatrixInfinityMellinTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Matrix UpperHalfPlane SmallLevelOriginal SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct SmallLevelAdditive Complex Set MeasureTheory
open scoped MatrixGroups ModularForm

def sourceEntire (m : ℕ) (f : ℕ→ℂ) (r : ℝ) : ℂ→ℂ :=
  mellin (fun y : ℝ => fourier (fullCoefficients f (2*m)) ((r:ℂ)+(y:ℂ)*Complex.I))

/-- The source-to-infinity rows are genuinely entire Mellin integrals
derived from the original word laws. -/
theorem word_source_entire_of_fricke (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : IsSolution 33 (2*m) f) {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] (fricke 33 (by decide))=η • fourierFunction (2*m) f)
    (w : Word) (r : ℝ)
    (hC : (value w).val 1 0≠0)
    (hr : (value w).val 1 0*r+(value w).val 1 1=0) :
    Differentiable ℂ (sourceEntire m f r) := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  have hχ:=character_sign hη (root_unit hf.toEulerData 3) w
  have hn : character η (root 33 f 3) w≠0 := by
    rcases hχ with h|h <;> simp [h]
  have hd : (value w).val 0 0*(value w).val 1 1-
      (value w).val 0 1*(value w).val 1 0=(1:ℝ) := by
    have hh:=value_det w
    change (value w).val.det=1 at hh
    simpa only [det_fin_two] using hh
  exact QuantitativeArithmeticMatrixInfinityMellin.matrix_source_entire
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m))
    (2*m) (by omega) ((value w).val 0 0) ((value w).val 0 1)
    ((value w).val 1 0) ((value w).val 1 1) r hC (by rw [hd]; norm_num)
    hr (character η (root 33 f 3) w) hn
    (word_fourier_of_slash m f η (root 33 f 3) hη (root_unit hf.toEulerData 3) w (words_of_fricke hm hf η hη hW w))

theorem sourceEntire_initial (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 33 (2*m) f) :
    ∃ B : ℝ, ∀ r : ℝ, ∀ s : ℂ, B<s.re →
      sourceEntire m f r s=original (2*m) f r s := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  obtain ⟨B,hB⟩:=SmallLevelTaylor.additive_convergence_halfplane
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m))
  exact ⟨B,fun r s hs => (hB r s hs).2⟩

#print axioms word_source_entire_of_fricke
#print axioms sourceEntire_initial
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
