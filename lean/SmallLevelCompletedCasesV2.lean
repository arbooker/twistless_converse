module

public import SmallLevelCompletedCasesTheoryV4
public import QuantitativeArithmeticLevelTwentyOneConverseV4

set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelCompletedCasesV2
open FinitenessOriginalInput SmallLevelOriginal QuantitativeArithmeticSmallLevelCirc

/-- Completed levels with the full level21 converse added. -/
def completed : Finset ℕ := insert 21 SmallLevelCompletedCases.completed

theorem completed_card : completed.card=25 := by decide

theorem completed_positive {N : ℕ} (hN : N∈completed) : 0<N := by
  rcases Finset.mem_insert.mp hN with rfl|hN
  · omega
  · exact SmallLevelCompletedCases.completed_positive hN

theorem modular {N k : ℕ} (hN : N∈completed) (hk : 0<k) (heven : Even k)
    {f : ℕ → ℂ} (hf : IsSolution N k f) : IsModular N k f := by
  rcases Finset.mem_insert.mp hN with rfl|hN
  · exact level_twenty_one hk heven hf
  · exact SmallLevelCompletedCases.modular hN hk heven hf

theorem circ {N k : ℕ} (hN : N∈completed) (hk : 0<k) (heven : Even k)
    {f : ℕ → ℂ} (hf : IsSolution N k f) : IsCirc N (completed_positive hN) k f :=
  original_modular_isCirc_even (completed_positive hN) hk heven hf (modular hN hk heven hf)

theorem exact_count {N k : ℕ} (hN : N∈completed) (hk : 0<k) (heven : Even k) :
    Finite (S N k) ∧ Nat.card (S N k)=Module.finrank ℂ (space N (completed_positive hN) k) :=
  original_count_eq (completed_positive hN) hk heven (fun _ hf => modular hN hk heven hf)

#print axioms completed_card
#print axioms modular
#print axioms circ
#print axioms exact_count
end SmallLevelCompletedCasesV2
