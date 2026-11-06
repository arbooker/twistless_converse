module
public import SmallLevelTwentySixGridWordTaylorV1
public import QuantitativeArithmeticMatrixInfinityMellinTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Matrix UpperHalfPlane SmallLevelOriginal SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct SmallLevelAdditive Complex Set MeasureTheory
open SmallLevelTwentySixTwelfth (W)
open scoped MatrixGroups ModularForm

def sourceEntire (m : ℕ) (f : ℕ→ℂ) (r : ℝ) : ℂ→ℂ :=
  mellin (fun y : ℝ => fourier (fullCoefficients f (2*m)) ((r:ℂ)+(y:ℂ)*Complex.I))

/-- The source-to-infinity rows are genuinely entire Mellin integrals
derived from the original word laws. -/
theorem word_source_entire_of_fricke (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : IsSolution 26 (2*m) f) {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=η • fourierFunction (2*m) f)
    (w : List (Fin 4×Bool)) (r : ℝ)
    (hC : (gridWord w).val 1 0≠0)
    (hr : (gridWord w).val 1 0*r+(gridWord w).val 1 1=0) :
    Differentiable ℂ (sourceEntire m f r) := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  have hχ:=gridWordSign_unit (root_unit hf.toEulerData 2) hη w
  have hn : gridWordSign (root 26 f 2) η w≠0 := by
    rcases hχ with h|h <;> simp [h]
  have hd : (gridWord w).val 0 0*(gridWord w).val 1 1-
      (gridWord w).val 0 1*(gridWord w).val 1 0=(1:ℝ) := by
    have hh:=gridWord_det w
    change (gridWord w).val.det=1 at hh
    simpa only [det_fin_two] using hh
  exact QuantitativeArithmeticMatrixInfinityMellin.matrix_source_entire
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m))
    (2*m) (by omega) ((gridWord w).val 0 0) ((gridWord w).val 0 1)
    ((gridWord w).val 1 0) ((gridWord w).val 1 1) r hC (by rw [hd]; norm_num)
    hr (gridWordSign (root 26 f 2) η w) hn
    (grid_word_fourier hχ (grid_words_of_fricke m hf hη hW w))

theorem sourceEntire_initial (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 26 (2*m) f) :
    ∃ B : ℝ, ∀ r : ℝ, ∀ s : ℂ, B<s.re →
      sourceEntire m f r s=original (2*m) f r s := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  obtain ⟨B,hB⟩:=SmallLevelTaylor.additive_convergence_halfplane
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m))
  exact ⟨B,fun r s hs => (hB r s hs).2⟩

#print axioms word_source_entire_of_fricke
#print axioms sourceEntire_initial
end SmallLevelTwentySixGrid
