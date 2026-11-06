module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic

open Filter Topology

/-- Absolute Chebyshev lower bound for the exact `primesBelow` count used
by the relative-prime-density predicate. -/
theorem eventually_primesBelow_chebyshev_lower :
    ∀ᶠ n : ℕ in atTop,
      (Real.log 2 / 4) * (n : ℝ) / Real.log n ≤ (n.primesBelow.card : ℝ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc : 0 < Real.log (2 : ℝ) / 4 := by positivity
  have hsmall := (Real.isLittleO_log_id_atTop.comp_tendsto
    (show Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop from tendsto_natCast_atTop_atTop)).bound hc
  filter_upwards [hsmall, eventually_ge_atTop (4 : ℕ)] with n hsmall hn
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hnsub : (n - 1 : ℕ) > 1 := by omega
  have hsublog : 0 < Real.log (n - 1 : ℕ) := Real.log_pos (by exact_mod_cast hnsub)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hsmall' : Real.log (n : ℝ) ≤ (Real.log 2 / 4) * (n : ℝ) := by
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs,
      abs_of_nonneg hnlog.le, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hsmall
  have hnum : (Real.log 2 / 4) * (n : ℝ) ≤
      (n - 1 : ℕ) * Real.log 2 - Real.log ((n - 1 : ℕ) + 1) := by
    rw [hcast, sub_add_cancel]
    nlinarith
  have hnum0 : 0 ≤ (n - 1 : ℕ) * Real.log 2 - Real.log ((n - 1 : ℕ) + 1) :=
    (by positivity : 0 ≤ (Real.log 2 / 4) * (n : ℝ)).trans hnum
  have hlogs : Real.log (n - 1 : ℕ) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < n - 1 by omega))
    exact_mod_cast Nat.sub_le n 1
  have hb := Chebyshev.pi_ge (n - 1)
  rw [Nat.primeCounting_sub_one] at hb
  rw [Nat.primesBelow_card_eq_primeCounting']
  exact (div_le_div_of_nonneg_right hnum hnlog.le).trans
    ((div_le_div_of_nonneg_left hnum0 hsublog hlogs).trans hb)

/-- An existential absolute-constant interface for the final shifted-prime
density assembly. The count and cutoff conventions are literal. -/
theorem exists_absolute_primesBelow_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) / Real.log n ≤ (n.primesBelow.card : ℝ) :=
  ⟨Real.log 2 / 4, by positivity, eventually_primesBelow_chebyshev_lower⟩

#print axioms eventually_primesBelow_chebyshev_lower
#print axioms exists_absolute_primesBelow_lower

end QuantitativeArithmetic
