module

public import QuantitativeHolomorphicScalingV1
public import Mathlib.Analysis.Asymptotics.Defs

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open Filter Asymptotics

/-- A precise analytic hypothesis, not an assertion that the finite-branch
trace theorem has been formalized.  It is the normalized two-parameter
bound needed from that theorem, multiplied by the weight. -/
def HasTwoParameterBoundAlong (l : Filter ℕ) (f : ℕ → ℝ) (δ : ℝ) : Prop :=
  ∃ K C X₀ : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
    ∀ᶠ k in l, ∀ X : ℝ, X₀ ≤ X →
      |f k| ≤ K * (k : ℝ) *
        ((Real.log X) ^ (-(2 * δ)) + bridgeError C (k : ℝ) X)

abbrev HasTwoParameterBound (f : ℕ → ℝ) (δ : ℝ) : Prop :=
  HasTwoParameterBoundAlong atTop f δ

theorem observationScale_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun k : ℕ => observationScale a (k : ℝ)) atTop atTop := by
  have hL : Tendsto (fun k : ℕ => Real.log (Real.log (k : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact Real.tendsto_exp_atTop.comp ((Real.tendsto_sqrt_atTop.comp hL).const_mul_atTop ha)

/-- Conditional scalar reduction.  This proves the uniform range of
exponents in the parameter calculation, but does not discharge
`HasTwoParameterBound` for the concrete Euler count. -/
theorem isBigO_of_two_parameter_bound_along {l : Filter ℕ} (hl : l ≤ atTop)
    {f : ℕ → ℝ} {δ : ℝ}
    (hδ : δ < 1 / 2) (hbound : HasTwoParameterBoundAlong l f δ) :
    f =O[l] (fun k : ℕ => remainderScale δ (k : ℝ)) := by
  obtain ⟨K, C, X₀, hK, hC, hb⟩ := hbound
  obtain ⟨a, ha, hCa⟩ := exists_scale_constant hC
  have hL : Tendsto (fun k : ℕ => Real.log (Real.log (k : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply IsBigO.of_bound (K * (a ^ (-(2 * δ)) + 1))
  filter_upwards [hb, (hL.eventually (eventually_ge_atTop 16)).filter_mono hl,
    ((observationScale_tendsto ha).eventually (eventually_ge_atTop X₀)).filter_mono hl,
    (eventually_ge_atTop 2).filter_mono hl] with k hbk hLk hX hk
  have hk' : 1 < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hL0 : 0 ≤ Real.log (Real.log (k : ℝ)) := by linarith
  have he : bridgeError C (k : ℝ) (observationScale a (k : ℝ)) ≤
      (Real.log (Real.log (k : ℝ))) ^ (-δ) :=
    (bridgeError_at_scale hk' hLk hCa).trans
      (power_saving_le_loglog hk' hLk (by linarith))
  have hr := regular_error_at_scale ha.le hL0 δ
  have hscale : 0 ≤ remainderScale δ (k : ℝ) := by
    exact mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hL0 _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hscale]
  calc
    |f k| ≤ K * (k : ℝ) *
        ((Real.log (observationScale a (k : ℝ))) ^ (-(2 * δ)) +
          bridgeError C (k : ℝ) (observationScale a (k : ℝ))) := hbk _ hX
    _ ≤ K * (k : ℝ) *
        (a ^ (-(2 * δ)) * (Real.log (Real.log (k : ℝ))) ^ (-δ) +
          (Real.log (Real.log (k : ℝ))) ^ (-δ)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (Nat.cast_nonneg k))
      rw [hr]
      exact add_le_add le_rfl he
    _ = (K * (a ^ (-(2 * δ)) + 1)) * remainderScale δ (k : ℝ) := by
      dsimp [remainderScale]
      ring

theorem isBigO_of_two_parameter_bound {f : ℕ → ℝ} {δ : ℝ}
    (hδ : δ < 1 / 2) (hbound : HasTwoParameterBound f δ) :
    f =O[atTop] (fun k : ℕ => remainderScale δ (k : ℝ)) :=
  isBigO_of_two_parameter_bound_along le_rfl hδ hbound

#print axioms observationScale_tendsto
#print axioms isBigO_of_two_parameter_bound_along
#print axioms isBigO_of_two_parameter_bound

end QuantitativeHolomorphic
