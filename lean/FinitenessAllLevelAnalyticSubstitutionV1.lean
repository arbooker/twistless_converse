module

public import FinitenessAllLevelHolomorphicReductionV1
public import Mathlib.Analysis.Analytic.Polynomial

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelAnalyticSubstitution

open ContinuousLinearMap Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Applying a holomorphic family of bounded linear maps is jointly
holomorphic in the parameter and in the finite-dimensional coordinate. -/
theorem joint_analytic {J : ℂ → E →L[ℂ] X} {U : Set ℂ}
    (hJ : AnalyticOnNhd ℂ J U) :
    AnalyticOnNhd ℂ (fun zv : ℂ × E => J zv.1 zv.2) (U ×ˢ univ) := by
  intro zv hzv
  have hfst : AnalyticAt ℂ (fun t : ℂ × E => t.1) zv := (fst ℂ ℂ E).analyticAt _
  have hsnd : AnalyticAt ℂ (fun t : ℂ × E => t.2) zv := (snd ℂ ℂ E).analyticAt _
  exact ((ContinuousLinearMap.id ℂ (E →L[ℂ] X)).analyticAt_bilinear (J zv.1, zv.2)).comp₂
    ((hJ zv.1 hzv.1).comp hfst) hsnd

/-- Substitution preserves one common domain for an arbitrary family of
analytic equations. It makes no assertion of local finite generation. -/
theorem substitute_analytic {J : ℂ → E →L[ℂ] X} {U : Set ℂ}
    (hJ : AnalyticOnNhd ℂ J U) {H : ℂ × X → ℂ}
    (hH : AnalyticOnNhd ℂ H (U ×ˢ univ)) :
    AnalyticOnNhd ℂ (fun zv : ℂ × E => H (zv.1, J zv.1 zv.2)) (U ×ˢ univ) := by
  intro zv hzv
  exact (hH _ ⟨hzv.1, mem_univ _⟩).comp
    (((fst ℂ ℂ E).analyticAt zv).prod (joint_analytic hJ zv hzv))

/-- Any polynomial in finitely many bounded coefficient functionals gives
an analytic equation after the holomorphic reconstruction substitution. -/
theorem polynomial_coordinates {ι : Type*} (c : ι → X →L[ℂ] ℂ)
    (p : MvPolynomial ι ℂ) {J : ℂ → E →L[ℂ] X} {U : Set ℂ}
    (hJ : AnalyticOnNhd ℂ J U) :
    AnalyticOnNhd ℂ (fun zv : ℂ × E =>
      MvPolynomial.aeval (fun i => c i (J zv.1 zv.2)) p) (U ×ˢ univ) := by
  intro zv hzv
  exact AnalyticAt.aeval_mvPolynomial (fun i =>
    ((c i).analyticAt _).comp (joint_analytic hJ zv hzv)) p

#print axioms joint_analytic
#print axioms substitute_analytic
#print axioms polynomial_coordinates

end FinitenessAllLevelAnalyticSubstitution
