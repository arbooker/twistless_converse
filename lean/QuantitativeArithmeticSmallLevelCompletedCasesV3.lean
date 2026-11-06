module
public import SmallLevelCompletedCasesV2
public import QuantitativeArithmeticLevelNineteenConverseV4
public import QuantitativeArithmeticLevelTwentyTwoConverseV4
public import QuantitativeArithmeticLevelTwentyFiveConverseV4
public import QuantitativeArithmeticLevelTwentySevenConverseV4
public import QuantitativeArithmeticLevelTwentyEightConverseV4
public import QuantitativeArithmeticLevelThirtyThreeConverseV4
public import QuantitativeArithmeticLevelThirtyFourConverseV4
public import QuantitativeArithmeticLevelThirtyFiveConverseV4
set_option autoImplicit false
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCompleted
open FinitenessOriginalInput SmallLevelOriginal QuantitativeArithmeticSmallLevelCirc

/-- All required levels except level26, which is combined separately. -/
def completed : Finset ℕ := {19,22,25,27,28,33,34,35} ∪ SmallLevelCompletedCasesV2.completed

theorem completed_card : completed.card=33 := by decide

theorem completed_iff (N : ℕ) : N∈completed ↔ 0<N ∧ N≤36 ∧ N≠26 ∧ N≠29 ∧ N≠31 := by
  simp only [completed,SmallLevelCompletedCasesV2.completed,SmallLevelCompletedCases.completed,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem completed_positive {N : ℕ} (hN : N∈completed) : 0<N := ((completed_iff N).mp hN).1

/-- Original-input modularity at every completed level. No continuation,
pole-bound or finite-certificate assumptions are added. -/
theorem modular {N k : ℕ} (hN : N∈completed) (hk : 0<k) (heven : Even k)
    {f : ℕ→ℂ} (hf : IsSolution N k f) : IsModular N k f := by
  rcases Finset.mem_union.mp hN with hN|hN
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hN
    rcases hN with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact QuantitativeArithmeticSmallLevelNineteen.original_modular_all hk heven hf
    · exact level_twenty_two hk heven hf
    · obtain ⟨m,hm⟩ := heven
      have hkm : k=2*m := by omega
      rw [hkm] at hf ⊢
      exact QuantitativeArithmeticSmallLevelTwentyFive.original_modular (by omega) hf
    · exact QuantitativeArithmeticSmallLevelTwentySevenOrbit.level_twenty_seven hk heven hf
    · exact SmallLevelOriginal.level_twenty_eight hk heven hf
    · exact QuantitativeArithmeticSmallLevelThirtyThreeGroup.level_thirty_three hk heven hf
    · exact SmallLevelThirtyFourChiThree.level_thirty_four hk heven hf
    · exact QuantitativeArithmeticSmallLevelThirtyFiveGroup.level_thirty_five hk heven hf
  · exact SmallLevelCompletedCasesV2.modular hN hk heven hf

/-- The paper's target space, including both trace conditions and cusp
vanishing at zero and infinity, in every positive even weight. -/
theorem circ {N k : ℕ} (hN : N∈completed) (hk : 0<k) (heven : Even k)
    {f : ℕ→ℂ} (hf : IsSolution N k f) : IsCirc N (completed_positive hN) k f :=
  original_modular_isCirc_even (completed_positive hN) hk heven hf (modular hN hk heven hf)

/-- The arbitrary-level normalized eigenbasis theorem supplies the count. -/
theorem exact_count {N k : ℕ} (hN : N∈completed) (hk : 0<k) (heven : Even k) :
    Finite (S N k) ∧ Nat.card (S N k)=Module.finrank ℂ (space N (completed_positive hN) k) :=
  original_count_eq (completed_positive hN) hk heven (fun _ hf => modular hN hk heven hf)
#print axioms completed_card
#print axioms completed_iff
#print axioms modular
#print axioms circ
#print axioms exact_count
end QuantitativeArithmeticSmallLevelCompleted
