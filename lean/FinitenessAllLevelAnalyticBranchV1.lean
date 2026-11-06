module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelAnalyticBranch

open Complex Set Filter
open scoped Topology ContDiff

/-- An analytic equation with invertible fiber derivative has an actual
holomorphic local branch, including uniqueness in a product neighborhood.
The branch is constructed by the analytic implicit function theorem. -/
theorem analytic_branch {F : ℂ × ℂ → ℂ} {w x : ℂ}
    (hF : AnalyticAt ℂ F (w, x)) (hz : F (w, x) = 0)
    (hi : (fderiv ℂ F (w, x) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible) :
    ∃ b : ℂ → ℂ, b w = x ∧ AnalyticAt ℂ b w ∧
      (∀ᶠ z in 𝓝 w, F (z, b z) = 0) ∧
      ∀ᶠ t in 𝓝 (w, x), F t = 0 ↔ b t.1 = t.2 := by
  have hc : ContDiffAt ℂ ω F (w, x) := hF.contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  refine ⟨hc.implicitFunction hn hi, hc.implicitFunction_apply_self hn hi,
    (hc.contDiffAt_implicitFunction hn hi).analyticAt, ?_, ?_⟩
  · simpa only [hz] using hc.eventually_apply_implicitFunction hn hi
  · simpa only [hz] using hc.eventually_apply_eq_iff_implicitFunction hn hi

#print axioms analytic_branch

theorem scalar_isInvertible (L : ℂ →L[ℂ] ℂ) (hL : L 1 ≠ 0) : L.IsInvertible := by
  have he (z : ℂ) : L z = z * L 1 := by
    simpa only [smul_eq_mul, mul_one] using L.map_smul z (1 : ℂ)
  let G : ℂ →L[ℂ] ℂ := (L 1)⁻¹ • ContinuousLinearMap.id ℂ ℂ
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := G)
  · apply ContinuousLinearMap.ext
    intro z
    change L ((L 1)⁻¹ * z) = z
    rw [he]
    field_simp
  · apply ContinuousLinearMap.ext
    intro z
    change (L 1)⁻¹ * L z = z
    rw [he z]
    field_simp

/-- The derivative condition for a scalar branch reduces to the usual
nonvanishing partial derivative, rather than an abstract inverse assumption. -/
theorem simple_branch {F : ℂ × ℂ → ℂ} {w x : ℂ}
    (hF : AnalyticAt ℂ F (w, x)) (hz : F (w, x) = 0)
    (hd : deriv (fun y => F (w, y)) x ≠ 0) :
    ∃ b : ℂ → ℂ, b w = x ∧ AnalyticAt ℂ b w ∧
      (∀ᶠ z in 𝓝 w, F (z, b z) = 0) ∧
      ∀ᶠ t in 𝓝 (w, x), F t = 0 ↔ b t.1 = t.2 := by
  apply analytic_branch hF hz
  apply scalar_isInvertible
  have hh : HasFDerivAt (fun y => F (w, y))
      (fderiv ℂ F (w, x) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ) x := by
    convert! hF.differentiableAt.hasFDerivAt.comp x
      ((hasFDerivAt_const w x).prodMk (hasFDerivAt_id x)) using 1
  simpa only [← hh.fderiv, fderiv_apply_one_eq_deriv] using hd

#print axioms scalar_isInvertible
#print axioms simple_branch

end FinitenessAllLevelAnalyticBranch
