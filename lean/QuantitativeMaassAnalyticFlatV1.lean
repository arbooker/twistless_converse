module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.Uniqueness

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace QuantitativeMaass

/-- A real analytic function on the line with all derivatives zero at one
point vanishes globally. This is the final scalar step of Cauchy uniqueness. -/
theorem analytic_line_zero_of_all_derivatives {f : ℝ → ℂ} {x : ℝ}
    (hf : AnalyticOnNhd ℝ f univ) (hzero : ∀ n : ℕ,iteratedDeriv n f x=0) :
    f=fun _ => 0 := by
  have ha := hf x (mem_univ x)
  have htop : analyticOrderAt f x=⊤ := by
    apply ENat.eq_top_iff_forall_ge.mpr
    intro n
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).mpr (fun i _ => hzero i)
  exact hf.eq_of_eventuallyEq analyticOnNhd_const (analyticOrderAt_eq_top.mp htop)

#print axioms analytic_line_zero_of_all_derivatives

end QuantitativeMaass
