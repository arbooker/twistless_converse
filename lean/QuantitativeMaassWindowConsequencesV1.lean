module

public import QuantitativeConcreteGoalsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set Filter QuantitativeConcreteGoals
open scoped Topology

namespace QuantitativeMaass

/-! Consequences of the literal Euler-window claim. These reductions do not
assert the still missing upper bound at general admissible levels. -/

theorem maassWindow_zero_subset (N σ : ℕ) (t ε : ℝ) (hε : 0 ≤ ε) :
    maassWindow N σ t 0 ⊆ maassWindow N σ t ε := by
  rintro p ⟨hp, hpt, hb⟩
  exact ⟨hp, ⟨hpt.1, hpt.2.trans (by linarith)⟩, hb⟩

/-- Summing the two literal parity counts doubles the leading coefficient. -/
theorem maassWindow_parity_sum (N : ℕ) (ε : ℝ → ℝ)
    (h0 : MaassWindowClaim N 0 ε) (h1 : MaassWindowClaim N 1 ε) :
    (∀ᶠ t in atTop, (maassWindow N 0 t (ε t)).Finite ∧
      (maassWindow N 1 t (ε t)).Finite) ∧
    Tendsto (fun t : ℝ =>
      (((maassWindow N 0 t (ε t)).ncard + (maassWindow N 1 t (ε t)).ncard : ℕ) : ℝ) /
        (t * ε t)) atTop
      (𝓝 (2 * AsymptoticTotalNewCorner.arithmeticCoefficient N)) := by
  refine ⟨h0.1.and h1.1, ?_⟩
  convert h0.2.add h1.2 using 1
  · funext t
    simp only [Nat.cast_add, add_div]
  · congr 1
    ring

theorem canonicalWidth_eventually_unit :
    ∀ᶠ t in atTop, 0 < canonicalWidth t ∧ canonicalWidth t ≤ 1 := by
  filter_upwards [canonicalWidth_properties.1,
    canonicalWidth_properties.2.1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht hu
  exact ⟨ht, hu.le⟩

/-- The shrinking-window estimate implies the stated individual-parameter
bound, by inclusion of the zero-width window. Finiteness is retained. -/
theorem maassWindow_pointwise_of_canonicalWidth (N σ : ℕ)
    (h : MaassWindowClaim N σ canonicalWidth) :
    (∀ᶠ r in atTop, (maassWindow N σ r 0).Finite) ∧
    Tendsto (fun r : ℝ => ((maassWindow N σ r 0).ncard : ℝ) / r)
      atTop (𝓝 0) := by
  have hfinite : ∀ᶠ r in atTop, (maassWindow N σ r 0).Finite := by
    filter_upwards [h.1, canonicalWidth_properties.1] with r hr he
    exact hr.subset (maassWindow_zero_subset N σ r _ he.le)
  refine ⟨hfinite, ?_⟩
  have hlim := h.2.mul canonicalWidth_properties.2.1
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact div_nonneg (Nat.cast_nonneg _) hr.le
  · filter_upwards [h.1, canonicalWidth_properties.1,
      eventually_gt_atTop (0 : ℝ)] with r hr he hr0
    have hn : ((maassWindow N σ r 0).ncard : ℝ) ≤
        ((maassWindow N σ r (canonicalWidth r)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard (maassWindow_zero_subset N σ r _ he.le) hr
    calc
      _ ≤ ((maassWindow N σ r (canonicalWidth r)).ncard : ℝ) / r :=
        div_le_div_of_nonneg_right hn hr0.le
      _ = _ := by field_simp

#print axioms maassWindow_zero_subset
#print axioms maassWindow_parity_sum
#print axioms canonicalWidth_eventually_unit
#print axioms maassWindow_pointwise_of_canonicalWidth

end QuantitativeMaass
