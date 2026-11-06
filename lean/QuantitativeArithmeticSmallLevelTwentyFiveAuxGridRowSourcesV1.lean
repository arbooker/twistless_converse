module

public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridRowModelV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex Set Filter SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData
open QuantitativeArithmeticSmallLevelTwentyFiveKnownWords

/-- All original physical rows on the 1050-grid, with analytic Taylor remainders.
No auxiliary twist continuation is assumed. -/
theorem original_row_sources {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (r : Row) :
    ∃ (B : ℝ) (H : ℕ → ℂ → ℂ),
      (∀ (M : ℕ) s, B-((M:ℝ)+1)<s.re → AnalyticAt ℂ (H M) s) ∧
      ∀ (M : ℕ) s, B<s.re →
        leading r m f ε s (gridVector 1050 (2*m) f s)=H M s+
          ∑ n∈Finset.range M, shifted r m f ε n s
            (gridVector 1050 (2*m) f (s+((n:ℂ)+1))) := by
  cases r with
  | word r =>
      obtain ⟨B,H,hH⟩ := certificate_rows (by decide : 0<1050) r hf ε hε hlaw
      refine ⟨B,H,fun M s hs => (hH M).1 s hs,?_⟩
      exact fun M s hs => (hH M).2 s hs
  | taylor r =>
      obtain ⟨B,hB⟩ := taylor_certificate_rows r hf ε hlaw
      refine ⟨B,taylorError 1050 (2*m) f ε r.q r.source,
        fun M s hs => (hB M).1 s hs,?_⟩
      exact fun M s hs => (hB M).2 s hs
  | entire q hq hqQ =>
      obtain ⟨he,B,hB⟩ := original_entire_row 1050 (by decide) (by omega) hf q hq hqQ
      refine ⟨B,fun _ => ramanujanEntire 25 (2*m) f q,
        fun _ s _ => he s,?_⟩
      intro M s hs
      simpa only [leading,shifted,Finset.sum_const_zero,add_zero] using hB s hs
  | hecke p hp hpQ j =>
      obtain ⟨B,hB⟩ := original_hecke_grid 1050 (by decide) hm hf hp hpQ
      refine ⟨B,fun _ _ => 0,fun _ _ _ => analyticAt_const,?_⟩
      intro M s hs
      simpa only [leading,shifted,Finset.sum_const_zero,add_zero,fullHeckeRow_grid] using hB j s hs
  | infinity w j hC hd =>
      have hden : QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.wordDen 1050 w j=0 := by
        by_contra hne
        exact ((QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.word_den_integer 1050 (by decide) w j).mp hne) hd
      have he := QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.original_word_source_entire 1050 hm hf w
        ((QuantitativeArithmeticSmallLevelTwentyFiveKnownWords.word_C_integer w).mpr hC) j hden
      obtain ⟨B,hB⟩ := original_common_halfplane hf
      refine ⟨B,fun _ => QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.sourceEntire 1050 (2*m) f j,
        fun _ s _ => he.analyticAt s,?_⟩
      intro M s hs
      simp only [leading,shifted,Finset.sum_const_zero,add_zero,gridVector_index]
      exact ((hB ((j:ℝ)/1050) s hs).2).symm

#print axioms original_row_sources
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
