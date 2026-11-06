module

public import QuantitativeHolomorphicTransferV1
public import QuantitativeHolomorphicPowerTraceV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open Filter Asymptotics

/-- The elementary sublevel proof gives a one-third power saving.
It permits exactly the same double-logarithmic observation scale. -/
def bridgeErrorThird (C k X : ℝ) : ℝ :=
  Real.exp (Real.exp (C * (Real.log X) ^ 2) - Real.log k / 3)

theorem exp_half_le_twelfth_exp {L : ℝ} (hL : 32 ≤ L) :
    Real.exp (L / 2) ≤ Real.exp L / 12 := by
  have he := Real.add_one_le_exp (L / 2)
  have hp := Real.exp_pos (L / 2)
  have hm : 0 ≤ Real.exp (L / 2) * (Real.exp (L / 2) - 12) :=
    mul_nonneg hp.le (by linarith)
  have hid : Real.exp L = Real.exp (L / 2) * Real.exp (L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hid]
  nlinarith

theorem bridgeErrorThird_at_scale {a C k : ℝ} (hk : 1 < k)
    (hL : 32 ≤ Real.log (Real.log k)) (hCa : C * a ^ 2 ≤ 1 / 2) :
    bridgeErrorThird C k (observationScale a k) ≤ Real.exp (-Real.log k / 4) := by
  have hlog : 0 < Real.log k := Real.log_pos hk
  have hL0 : 0 ≤ Real.log (Real.log k) := by linarith
  have hi : Real.exp (C * (Real.log (observationScale a k)) ^ 2) ≤ Real.log k / 12 := by
    rw [log_observationScale_sq a k hL0]
    calc
      Real.exp (C * (a ^ 2 * Real.log (Real.log k))) ≤
          Real.exp (Real.log (Real.log k) / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hCa hL0]
      _ ≤ Real.exp (Real.log (Real.log k)) / 12 := exp_half_le_twelfth_exp hL
      _ = Real.log k / 12 := by rw [Real.exp_log hlog]
  apply Real.exp_le_exp.mpr
  linarith

/-- Explicit remaining analytic hypothesis, now matching the proved
one-third-power finite-branch kernel bound.  This is not a theorem
that the Euler count satisfies this hypothesis. -/
def HasThirdPowerTwoParameterBoundAlong (l : Filter ℕ) (f : ℕ → ℝ) (δ : ℝ) : Prop :=
  ∃ K C X₀ : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
    ∀ᶠ k in l, ∀ X : ℝ, X₀ ≤ X →
      |f k| ≤ K * (k : ℝ) *
        ((Real.log X) ^ (-(2 * δ)) + bridgeErrorThird C (k : ℝ) X)

theorem isBigO_of_third_power_two_parameter_bound_along {l : Filter ℕ} (hl : l ≤ atTop)
    {f : ℕ → ℝ} {δ : ℝ}
    (hδ : δ < 1 / 2) (hbound : HasThirdPowerTwoParameterBoundAlong l f δ) :
    f =O[l] (fun k : ℕ => remainderScale δ (k : ℝ)) := by
  obtain ⟨K, C, X₀, hK, hC, hb⟩ := hbound
  obtain ⟨a, ha, hCa⟩ := exists_scale_constant hC
  have hL : Tendsto (fun k : ℕ => Real.log (Real.log (k : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply IsBigO.of_bound (K * (a ^ (-(2 * δ)) + 1))
  filter_upwards [hb, (hL.eventually (eventually_ge_atTop 32)).filter_mono hl,
    ((observationScale_tendsto ha).eventually (eventually_ge_atTop X₀)).filter_mono hl,
    (eventually_ge_atTop 2).filter_mono hl] with k hbk hLk hX hk
  have hk' : 1 < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hL0 : 0 ≤ Real.log (Real.log (k : ℝ)) := by linarith
  have he : bridgeErrorThird C (k : ℝ) (observationScale a (k : ℝ)) ≤
      (Real.log (Real.log (k : ℝ))) ^ (-δ) :=
    (bridgeErrorThird_at_scale hk' hLk hCa).trans
      (power_saving_le_loglog hk' (by linarith) (by linarith))
  have hr := regular_error_at_scale ha.le hL0 δ
  have hscale : 0 ≤ remainderScale δ (k : ℝ) := by
    exact mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hL0 _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hscale]
  calc
    |f k| ≤ K * (k : ℝ) *
        ((Real.log (observationScale a (k : ℝ))) ^ (-(2 * δ)) +
          bridgeErrorThird C (k : ℝ) (observationScale a (k : ℝ))) := hbk _ hX
    _ ≤ K * (k : ℝ) *
        (a ^ (-(2 * δ)) * (Real.log (Real.log (k : ℝ))) ^ (-δ) +
          (Real.log (Real.log (k : ℝ))) ^ (-δ)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (Nat.cast_nonneg k))
      rw [hr]
      exact add_le_add le_rfl he
    _ = (K * (a ^ (-(2 * δ)) + 1)) * remainderScale δ (k : ℝ) := by
      dsimp [remainderScale]
      ring

#print axioms bridgeErrorThird_at_scale
#print axioms isBigO_of_third_power_two_parameter_bound_along

end QuantitativeHolomorphic
