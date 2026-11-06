module

public import FinitenessCompletionCheckV1
public import AsymptoticSectorComparisonV1

set_option autoImplicit false

public section

namespace FinitenessPaperMain1

open Filter Asymptotics FinitenessOriginalInput
  AsymptoticSectorComparison

/-- The uniform version of `paper1.tex`, Theorem `thm:main1`.
The constant is chosen before the positive even weight. The counted set is
the original complex Euler-product solution set, with no auxiliary inputs. -/
theorem uniform_bound (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, 0 < k → Even k →
      (S N k).Finite ∧ (S N k).ncard ≤ C * k :=
  FinitenessOriginalTheorem.even_weight N hN.1 hN.2.1 hN.2.2

/-- The literal count is `O_N(k)` as the weight tends to infinity through
the even integers. This follows from the all-positive-weight bound, without
using the stronger asymptotic count or a classical dimension formula. -/
theorem count_isBigO (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    (fun k : ℕ => ((S N k).ncard : ℝ))
      =O[evenWeights] (fun k : ℕ => (k : ℝ)) := by
  obtain ⟨C, _hC, hbound⟩ := uniform_bound N hN
  apply IsBigO.of_bound (C : ℝ)
  have hpos : ∀ᶠ k : ℕ in evenWeights, 0 < k :=
    (eventually_gt_atTop 0).filter_mono inf_le_left
  have heven : ∀ᶠ k : ℕ in evenWeights, Even k :=
    (Filter.eventually_principal.mpr (fun _ hk => hk)).filter_mono inf_le_right
  filter_upwards [hpos, heven] with k hk he
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (S N k).ncard from Nat.cast_nonneg _),
    abs_of_nonneg (show (0 : ℝ) ≤ k from Nat.cast_nonneg _), Nat.cast_mul]
    using (show ((S N k).ncard : ℝ) ≤ (C * k : ℕ) by
      exact_mod_cast (hbound k hk he).2)

/-- `paper1.tex`, Theorem `thm:main1`: finiteness at every positive even
weight, together with the Big-O assertion for the same original predicate. -/
theorem main1 (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    (∀ k : ℕ, 0 < k → Even k →
      {f : ℕ → ℂ | IsSolution N k f}.Finite) ∧
    (fun k : ℕ => ({f : ℕ → ℂ | IsSolution N k f}.ncard : ℝ))
      =O[evenWeights] (fun k : ℕ => (k : ℝ)) := by
  obtain ⟨C, _hC, hbound⟩ := uniform_bound N hN
  exact ⟨fun k hk he => (hbound k hk he).1, count_isBigO N hN⟩

#print axioms uniform_bound
#print axioms count_isBigO
#print axioms main1

end FinitenessPaperMain1
