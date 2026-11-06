module

public import QuantitativeHolomorphicUniformTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open AsymptoticUnweightedKernel

theorem reciprocal_le_trace_power (h : ℕ) :
    1 / (h + 1 : ℝ) ≤ (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have he := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ h + 1 by linarith [Nat.cast_nonneg (α := ℝ) h]) (show (-1 : ℝ) ≤ -(1 / 3 : ℝ) by norm_num)
  simpa only [Real.rpow_neg_one, one_div] using he

theorem geometric_tail_le_trace_power (h : ℕ) :
    (1 / 2 : ℝ) ^ (2 * h) ≤ (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hp : (h + 1 : ℝ) ≤ (4 : ℝ) ^ h := by
    induction h with
    | zero => norm_num
    | succ n ih =>
      push_cast
      rw [pow_succ]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    (1 / 2 : ℝ) ^ (2 * h) = (1 / (4 : ℝ)) ^ h := by rw [pow_mul]; norm_num
    _ = 1 / (4 : ℝ) ^ h := one_div_pow _ _
    _ ≤ 1 / (h + 1 : ℝ) := one_div_le_one_div_of_le (by positivity) hp
    _ ≤ _ := reciprocal_le_trace_power h

theorem diagonal_denominator_le_trace_power {H : ℝ} (hH : 0 < H) (h : ℕ) :
    1 / (1 + (h : ℝ) / (4 * H ^ 2)) ≤
      (1 + 4 * H ^ 2) * (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hA : 0 < 4 * H ^ 2 := by positivity
  have hn : 0 < (h + 1 : ℝ) := by positivity
  have hd : 0 < 1 + (h : ℝ) / (4 * H ^ 2) := by positivity
  have hb : 1 / (1 + (h : ℝ) / (4 * H ^ 2)) ≤ (1 + 4 * H ^ 2) / (h + 1 : ℝ) := by
    apply (div_le_div_iff₀ hd hn).mpr
    have he : (1 + 4 * H ^ 2) * (1 + (h : ℝ) / (4 * H ^ 2)) =
        1 + 4 * H ^ 2 + h + (h : ℝ) / (4 * H ^ 2) := by field_simp; ring
    rw [he]
    nlinarith [div_nonneg (Nat.cast_nonneg (α := ℝ) h) hA.le]
  exact hb.trans (by simpa only [div_eq_mul_inv, one_div, one_mul] using
    mul_le_mul_of_nonneg_left (reciprocal_le_trace_power h) (by positivity : 0 ≤ 1 + 4 * H ^ 2))

def diagonalPowerCoefficient (Y H : ℝ) : ℝ :=
  ((compactKernelBound Y H 0 * (1 + 4 * H ^ 2) + 1) * Y⁻¹) / (4 * Real.pi)

def offDiagonalPowerCoefficient (D Y H : ℝ) (count : ℕ) : ℝ :=
  ((count : ℝ) * ((1 / Y) ^ 2 * (2 * Real.pi * D + Real.pi * D ^ 2) + 4 * H ^ 2 * Y⁻¹) +
    compactKernelBound Y H 1 * Y⁻¹) / (4 * Real.pi)

/-- An explicit polynomial geometric coefficient times a fixed power
saving in the weight; the infinite periodization tail is absorbed. -/
theorem uniformRetainedTraceError_le_power {D Y H : ℝ}
    (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H) (h count : ℕ) :
    uniformRetainedTraceError D Y H h count ≤
      (diagonalPowerCoefficient Y H + offDiagonalPowerCoefficient D Y H count) *
        (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) := by
  let r : ℝ := (h + 1 : ℝ) ^ (-(1 / 3 : ℝ))
  have hr : 0 ≤ r := by positivity
  have hK0 := compactKernelBound_nonneg Y H 0
  have hK1 := compactKernelBound_nonneg Y H 1
  have hdiag : diagonalTraceError Y H Y⁻¹ h ≤ diagonalPowerCoefficient Y H * r := by
    have hk : 1 / ((2 * h + 2 : ℕ) : ℝ) ≤ r := by
      apply (one_div_le_one_div_of_le (by positivity : 0 < (h + 1 : ℝ)) ?_).trans
        (reciprocal_le_trace_power h)
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) h]
    have hden := diagonal_denominator_le_trace_power hH h
    unfold diagonalTraceError diagonalPowerCoefficient
    calc
      _ = (compactKernelBound Y H 0 * Y⁻¹ * (1 / (1 + (h : ℝ) / (4 * H ^ 2))) +
          Y⁻¹ * (1 / ((2 * h + 2 : ℕ) : ℝ))) / (4 * Real.pi) := by ring
      _ ≤ (compactKernelBound Y H 0 * Y⁻¹ * ((1 + 4 * H ^ 2) * r) + Y⁻¹ * r) /
          (4 * Real.pi) := by gcongr
      _ = _ := by ring
  have hoff : periodizedBranchError D Y H 1 Y⁻¹ h count / (4 * Real.pi) ≤
      offDiagonalPowerCoefficient D Y H count * r := by
    have htail := geometric_tail_le_trace_power h
    unfold periodizedBranchError branchIntegralError offDiagonalPowerCoefficient
    calc
      _ ≤ ((count : ℝ) * (((1 / Y) ^ 2 * (2 * Real.pi * D + Real.pi * D ^ 2) +
          4 * H ^ 2 * Y⁻¹) * r) + (r * compactKernelBound Y H 1) * Y⁻¹) /
          (4 * Real.pi) := by gcongr
      _ = _ := by ring
  have hc0 : 0 ≤ diagonalPowerCoefficient Y H := by unfold diagonalPowerCoefficient; positivity
  have hc1 : 0 ≤ offDiagonalPowerCoefficient D Y H count := by unfold offDiagonalPowerCoefficient; positivity
  unfold uniformRetainedTraceError
  apply max_le
  · exact hdiag.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hc1) hr)
  · exact hoff.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hc0) hr)

/-- The resulting weight power saving for the actual two retained traces. -/
theorem retained_expression_power_trace_bound (e : AsymptoticFiniteBranch.Expression)
    {ε D Y H : ℝ} (hε : 0 < ε) (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H)
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H 1 ≤ 1 + |(n : ℝ)|)
    (geom : ∀ b ∈ e, b.label ≠ 1 → RetainedBranchGeometry b Y H D S) :
    |liftedTrace h hε (AsymptoticFiniteBranch.holomorphicSum
        (AsymptoticFiniteBranch.retainedExpression Y H e) (h + 1)) /
        ((2 * h + 2 : ℕ) : ℝ) -
      AsymptoticRegularTrace.signedTrace MeasureTheory.volume
        (AsymptoticFiniteBranch.regularSum (AsymptoticFiniteBranch.retainedExpression Y H e)) /
        (4 * Real.pi)| ≤
      ((AsymptoticFiniteBranch.expressionBound e + (e.length : ℝ)) *
        (diagonalPowerCoefficient Y H + offDiagonalPowerCoefficient D Y H S.card)) *
        (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have ht := retained_expression_uniform_trace_bound e hε hD hY hH h hsmall S hfar geom
  have hc : 0 ≤ AsymptoticFiniteBranch.expressionBound e + (e.length : ℝ) :=
    add_nonneg (AsymptoticFiniteBranch.expressionBound_nonneg e) (Nat.cast_nonneg _)
  exact ht.trans ((mul_le_mul_of_nonneg_left
    (uniformRetainedTraceError_le_power hD hY hH h S.card) hc).trans_eq (mul_assoc _ _ _).symm)

/-- A symmetric integer cutoff supplies the infinite-tail hypothesis. -/
theorem periodization_far_of_cutoff {Y H : ℝ} (N : ℕ)
    (hN : 2 * compactBaseBound Y H 1 ≤ (N : ℝ)) :
    ∀ n : ℤ, n ∉ Finset.Icc (-(N : ℤ)) N →
      2 * compactBaseBound Y H 1 ≤ 1 + |(n : ℝ)| := by
  intro n hn
  have ha : (N : ℤ) < |n| := by
    by_contra h
    have hb := abs_le.mp (le_of_not_gt h)
    exact hn (Finset.mem_Icc.mpr hb)
  have hr : (N : ℝ) < |(n : ℝ)| := by exact_mod_cast ha
  linarith

#print axioms retained_expression_power_trace_bound
#print axioms periodization_far_of_cutoff

#print axioms geometric_tail_le_trace_power
#print axioms diagonal_denominator_le_trace_power
#print axioms uniformRetainedTraceError_le_power

end QuantitativeHolomorphic
