module

public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

namespace FinitenessPaperConvergence

open Filter Asymptotics
open scoped Topology BigOperators

/-- Ordinary convergence of the positive-index Dirichlet series at some
complex argument. This permits conditional convergence; it does not assume
absolute convergence or a coefficient-growth estimate. -/
def ConvergesSomewhere (f : ℕ → ℂ) : Prop :=
  ∃ s z : ℂ, Tendsto (fun m : ℕ => ∑ n ∈ Finset.range m, LSeries.term f s n)
    atTop (𝓝 z)

/-- Convergence of partial sums forces the individual terms to tend to zero. -/
theorem terms_tendsto_zero {a : ℕ → ℂ} {z : ℂ}
    (h : Tendsto (fun m : ℕ => ∑ n ∈ Finset.range m, a n) atTop (𝓝 z)) :
    Tendsto a atTop (𝓝 0) := by
  have hd := (h.comp (tendsto_add_atTop_nat 1)).sub h
  simpa only [Function.comp_apply, Finset.sum_range_succ, add_sub_cancel_left,
    sub_self] using hd

/-- The paper's convergence hypothesis supplies the individual positive
polynomial-growth exponent used by the analytic formalization. -/
theorem growth_of_convergesSomewhere {f : ℕ → ℂ} (h : ConvergesSomewhere f) :
    ∃ σ : ℝ, 0 < σ ∧ f =O[atTop] (fun n : ℕ => (n : ℝ)^σ) := by
  obtain ⟨s, z, hz⟩ := h
  have ht := terms_tendsto_zero hz
  have hb : ∀ᶠ n in atTop, ‖LSeries.term f s n‖ < 1 := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp ht 1 zero_lt_one)
  refine ⟨max s.re 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  apply IsBigO.of_bound 1
  filter_upwards [hb, eventually_gt_atTop 0] with n hn hnpos
  have hnp : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hterm : ‖f n‖ / (n : ℝ)^s.re < 1 := by
    simpa only [LSeries.term, ite_eq_right (Nat.ne_of_gt hnpos), norm_div,
      Complex.norm_natCast_cpow_of_pos hnpos] using hn
  have hcoeff : ‖f n‖ < (n : ℝ)^s.re := by
    simpa only [one_mul] using
      (div_lt_iff₀ (Real.rpow_pos_of_pos hnp s.re)).mp hterm
  simpa only [one_mul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hnp (max s.re 1))] using
    hcoeff.le.trans (Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _))

/-- Conversely, polynomial growth gives absolute convergence sufficiently
far to the right, hence ordinary convergence somewhere. -/
theorem convergesSomewhere_of_growth {f : ℕ → ℂ} {σ : ℝ}
    (h : f =O[atTop] (fun n : ℕ => (n : ℝ)^σ)) : ConvergesSomewhere f := by
  have hs : LSeriesSummable f ((σ + 2 : ℝ) : ℂ) := by
    apply LSeriesSummable_of_isBigO_rpow (x := σ + 1)
    · simp only [Complex.ofReal_re]
      linarith
    · simpa only [add_sub_cancel_right] using h
  exact ⟨((σ + 2 : ℝ) : ℂ), _, hs.hasSum.tendsto_sum_nat⟩

theorem convergesSomewhere_iff_growth (f : ℕ → ℂ) :
    ConvergesSomewhere f ↔
      ∃ σ : ℝ, 0 < σ ∧ f =O[atTop] (fun n : ℕ => (n : ℝ)^σ) :=
  ⟨growth_of_convergesSomewhere, fun ⟨_, _, h⟩ => convergesSomewhere_of_growth h⟩

#print axioms terms_tendsto_zero
#print axioms growth_of_convergesSomewhere
#print axioms convergesSomewhere_iff_growth

end FinitenessPaperConvergence
