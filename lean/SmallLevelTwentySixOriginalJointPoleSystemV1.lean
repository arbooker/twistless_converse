module
public import SmallLevelTwentySixGermSourcesTheoryV4
public import SmallLevelTwentySixGridPoleSystemV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixOriginalJointPoleSystem
open Complex Matrix SmallLevelTwentySixUnitMMM
open SmallLevelTwentySixGrid

/-- Both continued row systems are constructed from the same original
Fricke sign and the same continued grid. No sign compatibility is assumed. -/
theorem original_joint_pole_system (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ ε : ℂ,(ε=1 ∨ ε= -1) ∧
      ∃ S : SmallLevelTwentySixGermSources.PoleSystem m f ε,
        ∃ T : SmallLevelTwentySixGrid.PoleSystem m f ε,S.G=T.G := by
  obtain ⟨ε,hε,hlaw⟩:=SmallLevelTwentySixGrid.original_grid_fricke_laws hf
  obtain ⟨B₁,E₁,_hF₁,hE₁,hrow₁⟩:=
    SmallLevelTwentySixGermSources.initial_system_of_laws m hm hf hε hlaw
  obtain ⟨B₂,E₂,_hF₂,hE₂,hrow₂⟩:=
    SmallLevelTwentySixGrid.initial_system_of_laws m hm hf hε hlaw
  obtain ⟨BG,G,hG,hGF⟩:=SmallLevelTwentySixGrid.original_grid_continuation m hm hf
  let S : SmallLevelTwentySixGermSources.PoleSystem m f ε := {
    B := max B₁ BG
    G := G
    E := fun n s i => E₁ i n s
    meromorphic := hG
    agreement := by
      intro z hz
      exact hGF z (lt_of_le_of_lt (le_max_right B₁ BG) hz)
    error := by
      intro n i z hz
      apply hE₁ n i z
      linarith [le_max_left B₁ BG]
    rows := by
      intro n s hs
      have hb : B₁<s.re:=lt_of_le_of_lt (le_max_left B₁ BG) hs
      change SmallLevelTwentySixGermSources.fullLeadingMatrix m f ε s *ᵥ
          (fun j => SmallLevelTwentySixGermSources.gridVector (2*m) f s (support j))=
        (fun i => E₁ i n s)+∑ j∈Finset.range n,
          SmallLevelTwentySixGermSources.fullShiftMatrix m f ε j s *ᵥ
            (fun i => SmallLevelTwentySixGermSources.gridVector (2*m) f (s+((j:ℂ)+1)) (support i))
      rw [SmallLevelTwentySixGermSources.fullLeadingMatrix_mulVec]
      simp_rw [SmallLevelTwentySixGermSources.fullShiftMatrix_mulVec]
      funext i
      simpa only [Pi.add_apply,Finset.sum_apply] using hrow₁ n s hb i
  }
  let T : SmallLevelTwentySixGrid.PoleSystem m f ε := {
    B := max B₂ BG
    G := G
    E := fun n s i => E₂ i n s
    meromorphic := hG
    agreement := by
      intro z hz
      exact hGF z (lt_of_le_of_lt (le_max_right B₂ BG) hz)
    error := by
      intro n i z hz
      apply hE₂ n i z
      linarith [le_max_left B₂ BG]
    rows := by
      intro n s hs
      have hb : B₂<s.re:=lt_of_le_of_lt (le_max_left B₂ BG) hs
      change SmallLevelTwentySixGrid.fullLeadingMatrix m f ε s *ᵥ
          (fun j => gridVector (2*m) f s (support j))=
        (fun i => E₂ i n s)+∑ j∈Finset.range n,
          SmallLevelTwentySixGrid.fullShiftMatrix m f ε j s *ᵥ
            (fun i => gridVector (2*m) f (s+((j:ℂ)+1)) (support i))
      rw [SmallLevelTwentySixGrid.fullLeadingMatrix_mulVec]
      simp_rw [SmallLevelTwentySixGrid.fullShiftMatrix_mulVec]
      funext i
      simpa only [Pi.add_apply,Finset.sum_apply] using hrow₂ n s hb i
  }
  exact ⟨ε,hε,S,T,rfl⟩

#print axioms original_joint_pole_system
end SmallLevelTwentySixOriginalJointPoleSystem
