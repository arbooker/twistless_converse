module
public import SmallLevelTwentySixUnitMMMTheoryV4
public import SmallLevelTwentySixUnitMMPTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex

/-- Global additive continuation on the common 320-coordinate support,
from the original level26 solution hypotheses, with all eight signs covered. -/
theorem original_grid_continuation (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ B : ℝ,∃ G : ℂ→Fin 320→ℂ,
      (∀ i x,MeromorphicNFAt (fun z => G z i) x) ∧
      ∀ z,B<z.re → G z=SmallLevelTwentySixUnitMMM.actualGrid m f z := by
  obtain ⟨ε,hε,hlaw⟩:=original_grid_fricke_laws hf
  have hη : phase m ε=1 ∨ phase m ε= -1 := grid_physical_sign m hε
  have h₂:=badParameter_two_sign hf.toEulerData
  have h₁₃:=badParameter_thirteen_sign hf.toEulerData
  rcases hη with hη|hη <;> rcases h₂ with h₂|h₂ <;> rcases h₁₃ with h₁₃|h₁₃
  · exact SmallLevelTwentySixUnitMMP.original_grid_continuation_scaled m hm hf hε hlaw
      (-1) (1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMM.original_grid_continuation_scaled m hm hf hε hlaw
      (-1) (1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMM.original_grid_continuation_scaled m hm hf hε hlaw
      (1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMP.original_grid_continuation_scaled m hm hf hε hlaw
      (1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMM.original_grid_continuation_scaled m hm hf hε hlaw
      (-1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMP.original_grid_continuation_scaled m hm hf hε hlaw
      (-1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMP.original_grid_continuation_scaled m hm hf hε hlaw
      (1) (1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMM.original_grid_continuation_scaled m hm hf hε hlaw
      (1) (1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)

#print axioms original_grid_continuation
end SmallLevelTwentySixGrid
