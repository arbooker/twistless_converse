module

public import FinitenessAllLevelGenericSeparableV1
public import FinitenessAllLevelAnalyticBranchV1
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCoefficientRing

open Complex Set Filter
open scoped Topology

variable {ι : Type*} {U : Set ℂ} (g : ι → ℂ → ℂ)

/-- The actual polynomial equation, using the analytic representatives of
its finitely many coefficient-ring elements. -/
def polynomialEquation (q : Polynomial (ring U g)) (t : ℂ × ℂ) : ℂ :=
  ∑ j ∈ q.support, representative U g (q.coeff j) t.1 * t.2 ^ j

theorem polynomialEquation_eq (q : Polynomial (ring U g)) (z : U) (x : ℂ) :
    polynomialEquation g q (z, x) = q.eval₂ (evaluation U g z) x := by
  simp only [polynomialEquation, Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [representative_agrees]
  rfl

theorem polynomialEquation_analytic (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    (q : Polynomial (ring U g)) {w x : ℂ} (hw : w ∈ U) :
    AnalyticAt ℂ (polynomialEquation g q) (w, x) := by
  apply Finset.analyticAt_fun_sum
  intro j _
  exact ((representative_analytic U g hg (q.coeff j) w hw).comp
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (w, x))).mul
      (((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (w, x)).pow j)

/-- Every root of a generically separable eliminant lies on an actual
holomorphic local root branch, unique in a neighborhood. This theorem does
not identify those root branches with branches of a whole equation system. -/
theorem eliminant_root_branch (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    (q : Polynomial (ring U g)) (w : U) (x : ℂ)
    (hs : (q.map (evaluation U g w)).Separable)
    (hx : q.eval₂ (evaluation U g w) x = 0) :
    ∃ b : ℂ → ℂ, b w = x ∧ AnalyticAt ℂ b w ∧
      (∀ᶠ z in 𝓝 w.val, polynomialEquation g q (z, b z) = 0) ∧
      ∀ᶠ t in 𝓝 (w.val, x), polynomialEquation g q t = 0 ↔ b t.1 = t.2 := by
  apply FinitenessAllLevelAnalyticBranch.simple_branch
    (polynomialEquation_analytic g hg q w.property)
    ((polynomialEquation_eq g q w x).trans hx)
  have he : (fun y => polynomialEquation g q (w.val, y)) =
      (fun y => (q.map (evaluation U g w)).eval y) := by
    funext y
    exact (polynomialEquation_eq g q w y).trans (Polynomial.eval₂_eq_eval_map _)
  rw [he, (q.map (evaluation U g w)).deriv]
  exact hs.eval₂_derivative_ne_zero (RingHom.id ℂ)
    (by simpa only [Polynomial.eval₂_id, ← Polynomial.eval₂_eq_eval_map] using hx)

#print axioms polynomialEquation_eq
#print axioms polynomialEquation_analytic
#print axioms eliminant_root_branch

end FinitenessAllLevelCoefficientRing
