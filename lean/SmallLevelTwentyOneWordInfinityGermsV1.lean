module

public import QuantitativeArithmeticMatrixInfinityMellinTheoryV4
public import SmallLevelTwentyOneWordGridGermsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Filter Set MeasureTheory SmallLevelAdditive SmallLevelTaylor
open FinitenessOriginalFourier FinitenessFourierConstruction
open SmallLevelTwentyOne
open scoped Topology

def sourceEntire (k : ℕ) (f : ℕ → ℂ) (t : ℤ) : ℂ → ℂ :=
  mellin (fun y : ℝ => fourier (fullCoefficients f k) ((((t:ℝ)/42:ℝ):ℂ)+(y:ℂ)*I))

theorem original_word_source_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (w : Word) (hC : coordC w≠0) (t : ℤ) (ht : wordDen w t=0) :
    Differentiable ℂ (sourceEntire (2*m) f t) := by
  obtain ⟨χ,hχ,hwords⟩ := original_words hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hne : character χ w≠0 := by
    rcases character_sign hχ w with hh|hh <;> simp [hh]
  unfold sourceEntire
  exact QuantitativeArithmeticMatrixInfinityMellin.matrix_source_entire
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m))
    (2*m) (by omega) (coordA w) (coordB w) (coordC w) (coordD w) ((t:ℝ)/42)
    hC (by rw [coordinate_det]; norm_num) ht (character χ w) hne
    (word_fourier_of_slash m f χ hχ w (hwords w))

/-- The source-to-infinity rows are entire on the actual continued grid;
these are the `ginf` rows in the finite pole system. -/
theorem original_word_infinity_germ {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (w : Word) (hC : coordC w≠0) (t : ℤ) (ht : wordDen w t=0) :
    (∀ x : ℂ, AnalyticAt ℂ (sourceEntire (2*m) f t) x) ∧
      ∀ x : ℂ, (fun s => G s (gridIndex t)) =ᶠ[𝓝[≠] x] sourceEntire (2*m) f t := by
  have hE := original_word_source_entire hm hf w hC t ht
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  refine ⟨fun x => hE.analyticAt x,?_⟩
  intro x
  apply SmallLevelContinuation.halfplane_germ_identity
    (x.re-1) (max B BG) _ _ _ x (by linarith)
  · intro z _
    exact (hG (gridIndex t) z).meromorphicAt
  · intro z _
    exact (hE.analyticAt z).meromorphicAt
  · intro z hz
    have hzB : B<z.re := lt_of_le_of_lt (le_max_left B BG) hz
    have hzG : BG<z.re := lt_of_le_of_lt (le_max_right B BG) hz
    dsimp only
    rw [hGF z hzG,gridVector_index]
    change original (2*m) f ((t:ℝ)/42) z=
      mellin (fun y : ℝ => fourier (fullCoefficients f (2*m)) ((((t:ℝ)/42:ℝ):ℂ)+(y:ℂ)*I)) z
    exact ((hB ((t:ℝ)/42) z hzB).2).symm

#print axioms original_word_source_entire
#print axioms original_word_infinity_germ
end SmallLevelTwentyOneKnownWords
