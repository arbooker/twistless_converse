module

public import QuantitativeArithmeticSmallLevelCircTheoryV4
public import QuantitativeArithmeticSmallLevelEighteenTheoryV4
public import QuantitativeArithmeticSmallLevelSeventeenTheoryV4
public import QuantitativeArithmeticSmallLevelThirteenTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyThreeTheoryV4
public import SmallLevelProgressCheckV20

/-! Consolidated chapter: SmallLevelCompletedCases. Original declarations and local scopes are retained. -/

/-! ## SmallLevelCompletedCasesV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelCompletedCases
open FinitenessOriginalInput SmallLevelOriginal

/-- The twenty-four levels whose converse theorems have been checked.
The ten outstanding levels are deliberately absent. -/
def completed : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 23, 24, 30, 32, 36}

theorem completed_card : completed.card = 24 := by decide

theorem completed_positive {N : ℕ} (hN : N ∈ completed) : 0 < N := by
  simp only [completed, Finset.mem_insert, Finset.mem_singleton] at hN
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Unconditional modularity from the original Euler input, at all
currently completed levels, every positive even weight and all cusps. -/
theorem modular {N k : ℕ} (hN : N ∈ completed) (hk : 0 < k)
    (heven : Even k) {f : ℕ → ℂ} (hf : IsSolution N k f) : IsModular N k f := by
  simp only [completed, Finset.mem_insert, Finset.mem_singleton] at hN
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SmallLevelOriginal.level_one heven hf
  · exact SmallLevelOriginal.level_two heven hf
  · exact SmallLevelOriginal.level_three heven hf
  · exact SmallLevelOriginal.level_four heven hf
  · exact SmallLevelOriginal.level_five heven hf
  · exact SmallLevelOriginal.level_six heven hf
  · exact SmallLevelOriginal.level_seven heven hf
  · exact SmallLevelOriginal.level_eight heven hf
  · exact SmallLevelOriginal.level_nine heven hf
  · exact SmallLevelOriginal.level_ten heven hf
  · exact SmallLevelOriginal.level_eleven hk heven hf
  · exact SmallLevelOriginal.level_twelve heven hf
  · exact QuantitativeArithmeticSmallLevelThirteen.level_thirteen hk heven hf
  · exact SmallLevelOriginal.level_fourteen hk heven hf
  · exact SmallLevelOriginal.level_fifteen hk heven hf
  · exact SmallLevelOriginal.level_sixteen heven hf
  · exact QuantitativeArithmeticSmallLevelSeventeen.level_seventeen hk heven hf
  · exact QuantitativeArithmeticSmallLevelEighteen.level_eighteen heven hf
  · exact SmallLevelOriginal.level_twenty hk heven hf
  · exact QuantitativeArithmeticSmallLevelTwentyThree.level_twenty_three hk heven hf
  · exact SmallLevelOriginal.level_twenty_four hk heven hf
  · exact SmallLevelOriginal.level_thirty hk heven hf
  · exact SmallLevelOriginal.level_thirty_two hk heven hf
  · exact SmallLevelThirtySix.level_thirty_six hk heven hf

#print axioms completed_card
#print axioms completed_positive
#print axioms modular
end SmallLevelCompletedCases
end
end

/-! ## SmallLevelCompletedCircCountV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelCompletedCases
open FinitenessOriginalInput QuantitativeArithmeticSmallLevelCirc

/-- Full trace-new membership, including weight two, for the twenty-four
completed levels. This imposes exactly the paper's two cusp vanishings. -/
theorem circ {N k : ℕ} (hN : N ∈ completed) (hk : 0 < k)
    (heven : Even k) {f : ℕ → ℂ} (hf : IsSolution N k f) :
    IsCirc N (completed_positive hN) k f :=
  original_modular_isCirc_even (completed_positive hN) hk heven hf
    (modular hN hk heven hf)

/-- The exact Euler solution count for every completed level and positive
even weight, using the arbitrary-level normalized eigenbasis theorem. -/
theorem exact_count {N k : ℕ} (hN : N ∈ completed) (hk : 0 < k)
    (heven : Even k) :
    Finite (S N k) ∧
      Nat.card (S N k) = Module.finrank ℂ (space N (completed_positive hN) k) :=
  original_count_eq (completed_positive hN) hk heven (fun _ hf => modular hN hk heven hf)

#print axioms circ
#print axioms exact_count
end SmallLevelCompletedCases
end
end
