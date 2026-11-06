module
public import QuantitativeArithmeticSmallLevelCompletedCasesV3
public import SmallLevelTwentySixOriginalModularV1
set_option autoImplicit false
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelAllCases
open FinitenessOriginalInput SmallLevelOriginal QuantitativeArithmeticSmallLevelCirc

/-- The exact level set in Theorem 1.3. This aggregate is not certified until
its full dependency closure, including level 26, passes the release check. -/
def levels : Finset ℕ := insert 26 QuantitativeArithmeticSmallLevelCompleted.completed

theorem levels_card : levels.card=34 := by decide

theorem levels_iff (N : ℕ) : N∈levels ↔ 0<N ∧ N≤36 ∧ N≠29 ∧ N≠31 := by
  simp only [levels, Finset.mem_insert, QuantitativeArithmeticSmallLevelCompleted.completed_iff]
  omega

theorem positive {N : ℕ} (hN : N∈levels) : 0<N := ((levels_iff N).mp hN).1

/-- Modularity from the original Euler-product and entire Fricke hypotheses. -/
theorem modular {N k : ℕ} (hN : N∈levels) (hk : 0<k) (heven : Even k)
    {f : ℕ→ℂ} (hf : IsSolution N k f) : IsModular N k f := by
  rcases Finset.mem_insert.mp hN with rfl | hN
  · exact SmallLevelTwentySixOriginal.level_twenty_six hk heven hf
  · exact QuantitativeArithmeticSmallLevelCompleted.modular hN hk heven hf

/-- Theorem 1.3 membership in the specified trace-zero space, with vanishing
at zero and infinity. No claim of cuspidality at every cusp is substituted. -/
theorem circ {N k : ℕ} (hN : N∈levels) (hk : 0<k) (heven : Even k)
    {f : ℕ→ℂ} (hf : IsSolution N k f) : IsCirc N (positive hN) k f :=
  original_modular_isCirc_even (positive hN) hk heven hf (modular hN hk heven hf)

/-- Theorem 1.3 exact count, using the general normalized eigenbasis theorem. -/
theorem exact_count {N k : ℕ} (hN : N∈levels) (hk : 0<k) (heven : Even k) :
    Finite (S N k) ∧ Nat.card (S N k)=Module.finrank ℂ (space N (positive hN) k) :=
  original_count_eq (positive hN) hk heven (fun _ hf => modular hN hk heven hf)

/-- The complete paper statement with explicit level and weight hypotheses.
Its dependency closure must pass before this draft counts as a formal proof. -/
theorem theorem13 {N k : ℕ} (hN : 0<N) (h36 : N≤36)
    (h29 : N≠29) (h31 : N≠31) (hk : 0<k) (heven : Even k) :
    (∀ f : ℕ→ℂ, IsSolution N k f → IsCirc N hN k f) ∧
    Finite (S N k) ∧ Nat.card (S N k)=Module.finrank ℂ (space N hN k) := by
  have hlevels : N∈levels := (levels_iff N).mpr ⟨hN,h36,h29,h31⟩
  exact ⟨fun f hf => circ hlevels hk heven hf, exact_count hlevels hk heven⟩

#print axioms theorem13
#print axioms levels_card
#print axioms levels_iff
#print axioms modular
#print axioms circ
#print axioms exact_count
end QuantitativeArithmeticSmallLevelAllCases
