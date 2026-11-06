module

public import SmallLevelBelowTenV1
public import SmallLevelTenModularV1
public import SmallLevelElevenModularV1
public import SmallLevelTwelveSixteenModularV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

/-- The full small-level conclusion for every level from one through twelve,
with the original Euler input, positive even weight and all cusp conditions. -/
theorem levels_one_to_twelve {N k : ℕ} (hN : 0<N) (hbound : N≤12)
    (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) : IsModular N k f := by
  by_cases hsmall : N≤9
  · exact levels_one_to_nine hN hsmall heven hf
  have hcases : N=10 ∨ N=11 ∨ N=12 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact level_ten heven hf
  · exact level_eleven hk heven hf
  · exact level_twelve heven hf

#print axioms levels_one_to_twelve

end SmallLevelOriginal
