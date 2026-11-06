module

public import SmallLevelTaylorRowNormalizationV1
public import Mathlib.Analysis.Analytic.Polynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Polynomial

theorem binomial_shift_analytic (k n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => Ring.choose (s+(n:ℂ)-(k:ℂ)) n) z := by
  simp_rw [Ring.choose_eq_smul,← Polynomial.aeval_eq_smeval]
  simpa only [Pi.smul_def] using ((show AnalyticAt ℂ (fun s : ℂ => s+(n:ℂ)-(k:ℂ)) z by fun_prop).aeval_polynomial (descPochhammer ℤ n)).const_smul (c := (n.factorial:ℂ)⁻¹)

def taylorRowScalar (k : ℕ) (L r : ℝ) (χ : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  χ*((L*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*(I*(L:ℂ)*(r:ℂ))^n*
    Ring.choose (s+(n:ℂ)-(k:ℂ)) n

/-- Every scalar coefficient used in the closed Taylor system is entire. -/
theorem taylorRowScalar_analytic (k : ℕ) {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (χ : ℂ) (n : ℕ) (z : ℂ) : AnalyticAt ℂ (taylorRowScalar k L r χ n) z := by
  have hc : ((L*r^2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (mul_pos hL (sq_pos_of_ne_zero hr)))
  have hp : AnalyticAt ℂ (fun s : ℂ => ((L*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))) z := by
    simp_rw [Complex.cpow_def_of_ne_zero hc]
    fun_prop
  exact ((analyticAt_const.mul hp).mul analyticAt_const).mul (binomial_shift_analytic k n z)

#print axioms binomial_shift_analytic
#print axioms taylorRowScalar_analytic
end SmallLevelTaylor
