module

public import SmallLevelTwentyOneAugmentedLeadingV1
public import SmallLevelUniversalPoleFirstShiftV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix Filter Set SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector
open scoped Topology

def augmentedShift (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) :
    Matrix AugmentedRow (Fin 42) ℂ
  | .inl i => wordShiftRow m (ε*I^(2*m)) (augmentedWordRows i).row n s
  | .inr (.inl _) => 0
  | .inr (.inr (.inl i)) =>
      let r := augmentedTaylorSpecs i
      ramanujanShiftRow m f ε r.1 r.2.1 (-(r.2.2/r.2.1)) n s
  | .inr (.inr (.inr _)) => 0

theorem augmented_row_germs {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z) (r : AugmentedRow) :
    ∃ (B : ℝ) (H : ℕ → ℂ → ℂ), ∀ M : ℕ,
      (∀ z, B-((M:ℝ)+1)<z.re → AnalyticAt ℂ (H M) z) ∧
      ∀ x, B-((M:ℝ)+1)<x.re →
        (fun z => ∑ j, augmentedLeading m f ε z r j*G z j)=ᶠ[𝓝[≠] x]
          (fun z => H M z+∑ a∈Finset.range M,
            ∑ j, augmentedShift m f ε a z r j*G (z+((a:ℂ)+1)) j) := by
  rcases r with i | i | i | i | i
  · let r := (augmentedWordRows i).row
    obtain ⟨B,H,he⟩ := integer_word_grid_germs hf ε hε hlaw BG G hG hGF
      r.word r.nonaffine r.source r.target r.denominator r.closed
    refine ⟨B,H,?_⟩
    intro M
    exact ⟨fun z hz => (he M).1 z hz,fun x hx => by
      simpa only [augmentedLeading,augmentedShift,wordLeadingRow_apply,wordShiftRow_apply]
        using (he M).2 x hx⟩
  · let r := augmentedInfinityRows i
    obtain ⟨hE,he⟩ := integer_word_infinity_germ hm hf BG G hG hGF
      r.word r.nonaffine r.source r.denominator
    refine ⟨0,fun _ => sourceEntire (2*m) f r.source,?_⟩
    intro M
    refine ⟨fun z _ => hE z,fun x _ => ?_⟩
    simpa [augmentedLeading,augmentedShift,r] using he x
  · obtain ⟨hq,hqQ,ht,hd,htd⟩ := augmentedTaylorSpecs_valid i
    obtain ⟨B,he⟩ := full_taylor_germs_of_law hf ε hlaw BG G hG hGF
      (augmentedTaylorSpecs i).1 hq hqQ (augmentedTaylorSpecs i).2.1
      (augmentedTaylorSpecs i).2.2 ht hd htd
    refine ⟨B,fullTaylorError (2*m) f ε (augmentedTaylorSpecs i).1 (augmentedTaylorSpecs i).2.1,?_⟩
    intro M
    exact ⟨fun z hz => (he M).1 z hz,fun x hx => by
      simpa only [augmentedLeading,augmentedShift,ramanujanLeadingRow_apply,ramanujanShiftRow_apply]
        using (he M).2 x hx⟩
  · obtain ⟨hE,he⟩ := original_full_entire_germs hm hf BG G hG hGF
      (augmentedEntireSpecs_valid i).1 (augmentedEntireSpecs_valid i).2
    refine ⟨0,fun _ => SmallLevelTaylor.ramanujanEntire 21 (2*m) f (augmentedEntireSpecs i),?_⟩
    intro M
    refine ⟨fun z _ => hE z,fun x _ => ?_⟩
    simpa [augmentedLeading,augmentedShift,samplingRow_apply,SmallLevelTwentyOne.sampleSum]
      using he x
  · refine ⟨0,fun _ _ => 0,?_⟩
    intro M
    refine ⟨fun _ _ => analyticAt_const,fun x _ => ?_⟩
    simpa [augmentedLeading,augmentedShift,heckeCoefficientRow_apply] using
      original_full_hecke_germs hm hf BG G hG hGF (augmentedHeckeSpecs_valid i).1
        (augmentedHeckeSpecs_valid i).2 (augmentedHeckeSpecs i).2 x

/-- The actual finite augmented Taylor system has one common half-plane
schedule for all rows and every shift order. -/
theorem augmented_matrix_germs {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z) :
    ∃ (B : ℝ) (H : ℕ → ℂ → AugmentedRow → ℂ),
      (∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z) ∧
      ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
        (fun z => ∑ j, augmentedLeading m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
          (fun z => H n z i+∑ a∈Finset.range n,
            ∑ j, augmentedShift m f ε a z i j*G (z+((a:ℂ)+1)) j) := by
  classical
  choose bounds errors he using augmented_row_germs hm hf ε hε hlaw BG G hG hGF
  obtain ⟨B,hB⟩ := (Set.finite_range bounds).bddAbove
  have hb (i : AugmentedRow) : bounds i≤B := hB (Set.mem_range_self i)
  refine ⟨B,fun n z i => errors i n z,?_,?_⟩
  · intro n i z hz
    exact (he i n).1 z (by linarith [hb i])
  · intro n i x hx
    exact (he i n).2 x (by linarith [hb i])

#print axioms augmented_row_germs
#print axioms augmented_matrix_germs
end SmallLevelTwentyOneKnownWords
