module
public import SmallLevelTwentySixGermSourcesTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Matrix SmallLevelTwentySixGrid SmallLevelTwentySixUnitMMM

/-- Construct the continued source system with a specified original
Fricke witness, so different source families use the same sign. -/
theorem pole_system_of_laws (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    {ε : ℂ} (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    Nonempty (PoleSystem m f ε) := by
  obtain ⟨B,E,_hF,hE,hrow⟩:=initial_system_of_laws m hm hf hε hlaw
  obtain ⟨BG,G,hG,hGF⟩:=original_grid_continuation m hm hf
  refine ⟨{
    B := max B BG
    G := G
    E := fun n s i => E i n s
    meromorphic := hG
    agreement := ?_
    error := ?_
    rows := ?_
  }⟩
  · intro z hz
    exact hGF z (lt_of_le_of_lt (le_max_right B BG) hz)
  · intro n i z hz
    apply hE n i z
    linarith [le_max_left B BG]
  · intro n s hs
    have hb : B<s.re:=lt_of_le_of_lt (le_max_left B BG) hs
    change fullLeadingMatrix m f ε s *ᵥ (fun j => gridVector (2*m) f s (support j))=
      (fun i => E i n s)+∑ j∈Finset.range n,
        fullShiftMatrix m f ε j s *ᵥ
          (fun i => gridVector (2*m) f (s+((j:ℂ)+1)) (support i))
    rw [fullLeadingMatrix_mulVec]
    simp_rw [fullShiftMatrix_mulVec]
    funext i
    simpa only [Pi.add_apply,Finset.sum_apply] using hrow n s hb i


#print axioms pole_system_of_laws
end SmallLevelTwentySixGrid
namespace SmallLevelTwentySixGermSources
open Complex Matrix SmallLevelTwentySixGrid SmallLevelTwentySixUnitMMM

/-- Construct the continued source system with a specified original
Fricke witness, so different source families use the same sign. -/
theorem pole_system_of_laws (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    {ε : ℂ} (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    Nonempty (PoleSystem m f ε) := by
  obtain ⟨B,E,_hF,hE,hrow⟩:=initial_system_of_laws m hm hf hε hlaw
  obtain ⟨BG,G,hG,hGF⟩:=original_grid_continuation m hm hf
  refine ⟨{
    B := max B BG
    G := G
    E := fun n s i => E i n s
    meromorphic := hG
    agreement := ?_
    error := ?_
    rows := ?_
  }⟩
  · intro z hz
    exact hGF z (lt_of_le_of_lt (le_max_right B BG) hz)
  · intro n i z hz
    apply hE n i z
    linarith [le_max_left B BG]
  · intro n s hs
    have hb : B<s.re:=lt_of_le_of_lt (le_max_left B BG) hs
    change fullLeadingMatrix m f ε s *ᵥ (fun j => gridVector (2*m) f s (support j))=
      (fun i => E i n s)+∑ j∈Finset.range n,
        fullShiftMatrix m f ε j s *ᵥ
          (fun i => gridVector (2*m) f (s+((j:ℂ)+1)) (support i))
    rw [fullLeadingMatrix_mulVec]
    simp_rw [fullShiftMatrix_mulVec]
    funext i
    simpa only [Pi.add_apply,Finset.sum_apply] using hrow n s hb i


#print axioms pole_system_of_laws
end SmallLevelTwentySixGermSources

namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid

/-- Both certified source families come from the original solution with
one common sign witness and the same actual continuation. -/
theorem original_compatible_pole_systems (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ ε : ℂ,(ε=1 ∨ ε= -1) ∧ GridFrickeLaws (2*m) f ε ∧
      ∃ (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε),S.G=T.G := by
  obtain ⟨ε,hε,hlaw⟩ := original_grid_fricke_laws hf
  obtain ⟨S⟩ := pole_system_of_laws m hm hf hε hlaw
  obtain ⟨T⟩ := SmallLevelTwentySixGrid.pole_system_of_laws m hm hf hε hlaw
  exact ⟨ε,hε,hlaw,S,T,S.grid_G_eq T⟩

#print axioms original_compatible_pole_systems
end SmallLevelTwentySixGermSources
