module
public import SmallLevelTwentySixGridTheoryV4
public import SmallLevelTwentySixOriginalJointPoleSystemV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixOriginal
open SmallLevelTwentySixGrid

/-- The original converse at level26, assembled from all eight sign choices.
This draft is complete only after its entire dependency closure passes Lean. -/
theorem even_weight (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    SmallLevelOriginal.IsModular 26 (2*m) f := by
  obtain ⟨ε,hε,S,T,_hG⟩ :=
    SmallLevelTwentySixOriginalJointPoleSystem.original_joint_pole_system m hm hf
  have hη : phase m ε=1 ∨ phase m ε= -1 := grid_physical_sign m hε
  have h₂ := badParameter_two_sign hf.toEulerData
  have h₁₃ := badParameter_thirteen_sign hf.toEulerData
  rcases hη with hη|hη <;> rcases h₂ with h₂|h₂ <;> rcases h₁₃ with h₁₃|h₁₃
  · exact T.modular_mmp S hm hf hε (-1) 1 (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact T.modular_mmm_small S hm hf (-1) 1 (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact T.modular_mmm_small S hm hf 1 (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact T.modular_mmp S hm hf hε 1 (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact T.modular_mmm_small S hm hf (-1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact T.modular_mmp S hm hf hε (-1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact T.modular_mmp S hm hf hε 1 1 (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact T.modular_mmm_small S hm hf 1 1 (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)

theorem level_twenty_six {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 k f) : SmallLevelOriginal.IsModular 26 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  exact even_weight m (by omega) hf

#print axioms even_weight
#print axioms level_twenty_six
end SmallLevelTwentySixOriginal
