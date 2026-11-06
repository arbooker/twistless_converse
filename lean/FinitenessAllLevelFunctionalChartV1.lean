module

public import FinitenessAllLevelCauchyChartV1
public import FinitenessAllLevelEquationSolutionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFunctionalChart

open Complex Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelGoodTrace
  FinitenessAllLevelFormalContinuation FinitenessAllLevelAnalyticSubstitution
  QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedReconstruction
  FinitenessAnalyticReconstruction

variable {N Q p : ℕ} {hQ : 0 < Q}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem evaluation_analytic (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (z : ℂ)
    {U : Set ℂ} {J : ℂ → E →L[ℂ] space (radius a)} (hJ : AnalyticOnNhd ℂ J U) :
    AnalyticOnNhd ℂ (fun t : ℂ × E => formal A P a χ m t.1 (J t.1 t.2) z)
      (U ×ˢ univ) :=
  substitute_analytic hJ ((formal_joint_analytic A P a χ m z).mono (subset_univ _))

theorem twist_analytic (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m q : ℕ) (z : ℂ)
    {U : Set ℂ} {J : ℂ → E →L[ℂ] space (radius a)} (hJ : AnalyticOnNhd ℂ J U) :
    AnalyticOnNhd ℂ (fun t : ℂ × E => twist (formal A P a χ m t.1 (J t.1 t.2)) q z)
      (U ×ˢ univ) := by
  intro t ht
  exact Finset.analyticAt_fun_sum _ (fun _ _ => evaluation_analytic A P a χ m _ hJ t ht)

/-- Every primitive Fricke equation is analytic on the same chart domain.
The spatial points, divisor and root-number sector are fixed parameters. -/
theorem fricke_analytic (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m q : ℕ) (z : ℂ)
    {U : Set ℂ} {J : ℂ → E →L[ℂ] space (radius a)} (hJ : AnalyticOnNhd ℂ J U) :
    AnalyticOnNhd ℂ (fun t : ℂ × E =>
      twist (formal A P a χ m t.1 (J t.1 t.2)) q z -
        χ q / (((Real.sqrt (Nat.lcm N (q ^ 2)) : ℝ) : ℂ) * z) ^ (2 * m) *
          twist (formal A P a χ m t.1 (J t.1 t.2)) q
            (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * z))) (U ×ˢ univ) :=
  (twist_analytic A P a χ m q z hJ).sub
    (analyticOnNhd_const.mul (twist_analytic A P a χ m q _ hJ))

/-- The complete Hecke equation, including both dilation terms, is
analytic on the very same domain as the Fricke and Cauchy equations. -/
theorem hecke_analytic (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (z : ℂ)
    {U : Set ℂ} {J : ℂ → E →L[ℂ] space (radius a)} (hJ : AnalyticOnNhd ℂ J U) :
    AnalyticOnNhd ℂ (fun t : ℂ × E =>
      completeTwist (formal A P a χ m t.1 (J t.1 t.2)) p z -
        (firstMultiplier (fun _ => t.1) m p *
          formal A P a χ m t.1 (J t.1 t.2) ((p : ℂ) * z) -
            (p : ℂ) ^ (2 * m) *
              formal A P a χ m t.1 (J t.1 t.2) ((p : ℂ) ^ 2 * z))) (U ×ˢ univ) := by
  intro t ht
  have hs : AnalyticAt ℂ (fun t : ℂ × E =>
      completeTwist (formal A P a χ m t.1 (J t.1 t.2)) p z) t :=
    Finset.analyticAt_fun_sum _ (fun _ _ => evaluation_analytic A P a χ m _ hJ t ht)
  have hm : AnalyticAt ℂ (fun t : ℂ × E => firstMultiplier (fun _ => t.1) m p) t := by
    exact analyticAt_const.mul ((ContinuousLinearMap.fst ℂ ℂ E).analyticAt t)
  exact hs.sub ((hm.mul (evaluation_analytic A P a χ m _ hJ t ht)).sub
    (analyticAt_const.mul (evaluation_analytic A P a χ m _ hJ t ht)))

#print axioms evaluation_analytic
#print axioms twist_analytic
#print axioms fricke_analytic
#print axioms hecke_analytic

end FinitenessAllLevelFunctionalChart
