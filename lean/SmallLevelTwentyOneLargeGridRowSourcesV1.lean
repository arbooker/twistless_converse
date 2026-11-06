module

public import SmallLevelTwentyOneLargeGridOldSourcesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneLargeGridModel
open Complex Set Filter SmallLevelTaylor SmallLevelAdditive
open SmallLevelTwentyOneFiniteGrid SmallLevelTwentyOneLargeGridData
open SmallLevelTwentyOneKnownWords

/-- Every row has an actual meromorphic source; its only possible source
singularity is the old-grid weight point. Positive Taylor shifts use the
same210-grid. No continuation of this larger grid is assumed. -/
theorem original_row_sources {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i s, MeromorphicNFAt (fun z => G z i) s)
    (hGF : ∀ s, BG<s.re → G s=SmallLevelTwentyOne.gridVector (2*m) f s)
    (hGreg : ∀ i s, s≠((2*m:ℕ):ℂ) → AnalyticAt ℂ (fun z => G z i) s)
    (r : Row) :
    ∃ (B : ℝ) (H : ℕ → ℂ → ℂ),
      (∀ (M : ℕ) s, B-((M:ℝ)+1)<s.re → MeromorphicAt (H M) s) ∧
      (∀ (M : ℕ) s, B-((M:ℝ)+1)<s.re → s≠((2*m:ℕ):ℂ) → AnalyticAt ℂ (H M) s) ∧
      ∀ (M : ℕ) s, B<s.re →
        leading r m f ε s (gridVector 210 (2*m) f s)=H M s+
          ∑ n∈Finset.range M, shifted r m f ε n s
            (gridVector 210 (2*m) f (s+((n:ℂ)+1))) := by
  cases r with
  | word r =>
      obtain ⟨B,H,hH⟩ := certificate_rows (by decide : 0<210) r hf ε hε hlaw
      refine ⟨B,H,fun M s hs => ((hH M).1 s hs).meromorphicAt,
        fun M s hs _ => (hH M).1 s hs,?_⟩
      exact fun M s hs => (hH M).2 s hs
  | taylor r =>
      obtain ⟨B,hB⟩ := taylor_certificate_rows r hf ε hlaw
      refine ⟨B,taylorError 210 (2*m) f ε r.q r.source,
        fun M s hs => ((hB M).1 s hs).meromorphicAt,
        fun M s hs _ => (hB M).1 s hs,?_⟩
      exact fun M s hs => (hB M).2 s hs
  | entire q hq hqQ =>
      obtain ⟨he,B,hB⟩ := original_entire_row 210 (by decide) (by omega) hf q hq hqQ
      refine ⟨B,fun _ => ramanujanEntire 21 (2*m) f q,
        fun _ s _ => (he s).meromorphicAt,fun _ s _ _ => he s,?_⟩
      intro M s hs
      simpa only [leading,shifted,Finset.sum_const_zero,add_zero] using hB s hs
  | hecke p hp hpQ j =>
      obtain ⟨B,hB⟩ := original_hecke_grid 210 (by decide) hm hf hp hpQ
      refine ⟨B,fun _ _ => 0,fun _ _ _ => analyticAt_const.meromorphicAt,
        fun _ _ _ _ => analyticAt_const,?_⟩
      intro M s hs
      simpa only [leading,shifted,Finset.sum_const_zero,add_zero,fullHeckeRow_grid] using hB j s hs
  | infinity w j hC hd =>
      have hden : SmallLevelTwentyOneFiniteGrid.wordDen 210 w j=0 := by
        by_contra hne
        exact ((SmallLevelTwentyOneFiniteGrid.word_den_integer 210 (by decide) w j).mp hne) hd
      have he := SmallLevelTwentyOneFiniteGrid.original_word_source_entire 210 hm hf w
        ((SmallLevelTwentyOneKnownWords.word_C_integer w).mpr hC) j hden
      obtain ⟨B,hB⟩ := original_common_halfplane hf
      refine ⟨B,fun _ => SmallLevelTwentyOneFiniteGrid.sourceEntire 210 (2*m) f j,
        fun _ s _ => (he.analyticAt s).meromorphicAt,
        fun _ s _ _ => he.analyticAt s,?_⟩
      intro M s hs
      simp only [leading,shifted,Finset.sum_const_zero,add_zero,gridVector_index]
      exact ((hB ((j:ℝ)/210) s hs).2).symm
  | old j =>
      refine ⟨BG,fun _ z => G z (SmallLevelTwentyOne.gridIndex j),
        fun _ s _ => (hG _ s).meromorphicAt,fun _ s _ hs => hGreg _ s hs,?_⟩
      intro M s hs
      simp only [leading,shifted,Finset.sum_const_zero,add_zero]
      rw [embedded_grid,hGF s hs]
  | heckeFive j =>
      obtain ⟨B,hB⟩ := original_five_source hm hf BG G hGF
      refine ⟨B,fun _ => oldFiveSource m f G j,
        fun _ s _ => oldFiveSource_meromorphic m f G hG j s,
        fun _ s _ hs => oldFiveSource_analytic m f G j s (fun i => hGreg i s hs),?_⟩
      intro M s hs
      simpa only [leading,shifted,Finset.sum_const_zero,add_zero] using hB j s hs

#print axioms original_row_sources
end SmallLevelTwentyOneLargeGridModel
