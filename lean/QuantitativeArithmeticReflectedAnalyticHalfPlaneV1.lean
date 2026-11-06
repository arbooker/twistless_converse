module
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticReflectedAnalyticHalfPlane

/-- A reflection identity transports analyticity across its central line.
This lemma makes no assertion that a meromorphic function is regular on
the initial half-plane; that is supplied by the pole-exclusion argument. -/
theorem analytic_everywhere_of_right_half_plane
    (F M : ℂ → ℂ) (C : ℂ) (b : ℝ) (hC : C.re=2*b)
    (hM : ∀ s, AnalyticAt ℂ M s)
    (hFE : ∀ s, F s=M s*F (C-s))
    (hR : ∀ s, b≤s.re → AnalyticAt ℂ F s) :
    ∀ s, AnalyticAt ℂ F s := by
  intro s
  by_cases hs : b≤s.re
  · exact hR s hs
  have hr : b≤(C-s).re := by
    simp only [Complex.sub_re,hC]
    linarith
  have haff : AnalyticAt ℂ (fun z : ℂ => C-z) s := by fun_prop
  have hc : AnalyticAt ℂ (fun z : ℂ => F (C-z)) s := (hR (C-s) hr).comp haff
  have hprod := (hM s).mul hc
  convert hprod using 1
  funext z
  exact hFE z

#print axioms analytic_everywhere_of_right_half_plane
end QuantitativeArithmeticReflectedAnalyticHalfPlane
