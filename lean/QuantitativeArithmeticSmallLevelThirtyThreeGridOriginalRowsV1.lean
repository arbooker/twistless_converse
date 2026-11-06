module
public import QuantitativeArithmeticSmallLevelThirtyThreeGridAssemblyV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Set SmallLevelAdditive SmallLevelTaylor

/-- Every selected source equation is derived from the original solution,
with the same coherent sign and an analytic Taylor remainder of every order. -/
theorem original_source_row (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    {ε : ℂ} (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε)
    (i : GridSource) :
    ∃ (B : ℝ) (error : ℕ→ℂ→ℂ),∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ,B<s.re →
        gridLeadingRows m f ε s (gridVector (2*m) f s) i=error M s+
          ∑ n∈Finset.range M,gridShiftRows m f ε n s
            (gridVector (2*m) f (s+((n:ℂ)+1))) i := by
  cases i with
  | word i =>
    obtain ⟨B,error,hB⟩:=grid_matrix_rows_of_fricke m hm hf (grid_physical_sign m hε)
      (grid_fricke_of_laws m hε hlaw) i
    refine ⟨B,error,fun M => ⟨(hB M).1,?_⟩⟩
    intro s hs
    simp only [gridLeadingRows,gridGroupLeading,gridShiftRows,gridVector_index]
    simpa only [gridVector] using (hB M).2 s hs
  | taylor i =>
    obtain ⟨B,hB⟩:=grid_ramanujan_rows_of_laws m hf hlaw i
    refine ⟨B,gridTaylorError m f ε i,fun M => ⟨(hB M).1,?_⟩⟩
    intro s hs
    simpa only [gridLeadingRows,gridRamanujanLeading,gridShiftRows,gridSample_grid] using (hB M).2 s hs
  | entire i =>
    obtain ⟨ha,B,hB⟩:=grid_ramanujan_entire m hm hf i
    refine ⟨B,fun _ => ramanujanEntire 33 (2*m) f (gridEntireQ i),?_⟩
    intro M
    refine ⟨fun s _ => ha s,?_⟩
    intro s hs
    simpa only [gridLeadingRows,gridShiftRows,Finset.sum_const_zero,add_zero,gridSample_grid]
      using (hB s hs).symm
  | hecke i =>
    obtain ⟨B,hB⟩:=original_grid_hecke_row m hm hf i
    refine ⟨B,fun _ _ => 0,?_⟩
    intro M
    refine ⟨fun _ _ => analyticAt_const,?_⟩
    intro s hs
    simpa only [gridLeadingRows,gridShiftRows,Finset.sum_const_zero,add_zero,gridHeckeLeading_grid]
      using hB s hs
  | infinity i =>
    have ha:=grid_infinity_entire_of_fricke m hm hf (grid_physical_sign m hε)
      (grid_fricke_of_laws m hε hlaw) i
    obtain ⟨B,hB⟩:=sourceEntire_initial m hf
    refine ⟨B,fun _ => sourceEntire m f (((gridInfinityIndex i:ℕ):ℝ)/66),?_⟩
    intro M
    refine ⟨fun s _ => ha.analyticAt s,?_⟩
    intro s hs
    simpa only [gridLeadingRows,gridShiftRows,Finset.sum_const_zero,add_zero,
      gridVector,grid,Int.cast_natCast,Nat.cast_ofNat] using
        (hB (((gridInfinityIndex i:ℕ):ℝ)/66) s hs).symm

/-- One common half-plane for all370 original equations. -/
theorem original_source_system (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ (ε : ℂ) (B : ℝ) (error : GridSource→ℕ→ℂ→ℂ),
      (ε=1 ∨ ε= -1) ∧ GridFrickeLaws (2*m) f ε ∧
      ∀ i : GridSource,∀ M : ℕ,
        AnalyticOnNhd ℂ (error i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
        ∀ s : ℂ,B<s.re →
          gridLeadingRows m f ε s (gridVector (2*m) f s) i=error i M s+
            ∑ n∈Finset.range M,gridShiftRows m f ε n s
              (gridVector (2*m) f (s+((n:ℂ)+1))) i := by
  obtain ⟨ε,hε,hlaw⟩:=original_grid_fricke_laws hf
  choose b error hb using original_source_row m hm hf hε hlaw
  have : Nonempty GridSource := ⟨.word 0⟩
  let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : GridSource) : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨ε,B,error,hε,hlaw,?_⟩
  intro i M
  constructor
  · intro s hs
    apply (hb i M).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M:ℝ)+1)<s.re
    linarith [hbB i]
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)

#print axioms original_source_row
#print axioms original_source_system
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
