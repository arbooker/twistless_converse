module

public import SmallLevelTwoThreeFourModularV1
public import SmallLevelFiveSevenNineModularV1
public import SmallLevelSixEightModularV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

/-- The completed initial range of the small-level theorem. The full
range through 36 remains a separate theorem, not a premise here. -/
theorem levels_one_to_nine {N k : ℕ} (hN : 0<N) (hbound : N≤9)
    (heven : Even k) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution N k f) :
    IsModular N k f := by
  interval_cases N
  · exact level_one heven hf
  · exact level_two heven hf
  · exact level_three heven hf
  · exact level_four heven hf
  · exact level_five heven hf
  · exact level_six heven hf
  · exact level_seven heven hf
  · exact level_eight heven hf
  · exact level_nine heven hf

#print axioms levels_one_to_nine

end SmallLevelOriginal
