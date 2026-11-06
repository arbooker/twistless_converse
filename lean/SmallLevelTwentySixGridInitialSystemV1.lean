module
public import SmallLevelTwentySixGridOriginalRowsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Set SmallLevelAdditive

/-- The original source system with a prescribed coherent sign and a common
half-plane that also provides analyticity of every original additive transform. -/
theorem initial_system_of_laws (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    {ε : ℂ} (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ (B : ℝ) (error : GridSource→ℕ→ℂ→ℂ),
      (∀ i : Fin 780,∀ z : ℂ,B<z.re → AnalyticAt ℂ (fun s => gridVector (2*m) f s i) z) ∧
      (∀ M : ℕ,∀ i : GridSource,∀ z : ℂ,B-((M:ℝ)+1)<z.re → AnalyticAt ℂ (error i M) z) ∧
      ∀ M : ℕ,∀ s : ℂ,B<s.re → ∀ i : GridSource,
        gridLeadingRows m f ε s (gridVector (2*m) f s) i=error i M s+
          ∑ n∈Finset.range M,gridShiftRows m f ε n s
            (gridVector (2*m) f (s+((n:ℂ)+1))) i := by
  choose b error hb using original_source_row m hm hf hε hlaw
  have : Nonempty GridSource := ⟨.word 0⟩
  let BS : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbS (i : GridSource) : b i≤BS:=Finset.le_sup' b (Finset.mem_univ i)
  obtain ⟨BF,hF⟩:=original_common_halfplane hf
  let B : ℝ:=max BS BF
  have hBS : BS≤B:=le_max_left _ _
  have hBF : BF≤B:=le_max_right _ _
  refine ⟨B,error,?_,?_,?_⟩
  · intro i z hz
    exact (hF (((i:ℕ):ℝ)/780) z (lt_of_le_of_lt hBF hz)).1
  · intro M i z hz
    apply (hb i M).1 z
    change b i-((M:ℝ)+1)<z.re
    linarith [hbS i]
  · intro M s hs i
    exact (hb i M).2 s (lt_of_le_of_lt ((hbS i).trans hBS) hs)

#print axioms initial_system_of_laws
end SmallLevelTwentySixGrid
