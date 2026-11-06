module

public import FinitenessAllLevelCauchyAnalyticV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCauchyConstraints

open Complex Metric Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelFormalContinuation
  QuantitativeArithmeticRetainedCertificate

theorem transform_kernel_integrable {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    {G : ℂ → ℂ} (hG : CircleIntegrable G c R) (hw : w ∈ ball c R) :
    CircleIntegrable (fun z => (z - w)⁻¹ • G z) c R := by
  apply hG.continuousOn_smul (g := fun z : ℂ => (z - w)⁻¹)
  apply (continuous_id.sub continuous_const).continuousOn.inv₀
  intro z hz
  apply sub_ne_zero.mpr
  intro he
  change z = w at he
  subst z
  have hh : dist w c = R := by simpa only [mem_sphere, abs_of_nonneg hR] using hz
  exact (ne_of_lt hw) hh

theorem transform_add {c w : ℂ} {R : ℝ} (hR : 0 ≤ R) {F G : ℂ → ℂ}
    (hF : CircleIntegrable F c R) (hG : CircleIntegrable G c R) (hw : w ∈ ball c R) :
    transform c R (F + G) w = transform c R F w + transform c R G w := by
  simp only [transform, Pi.add_apply, smul_add]
  rw [circleIntegral.integral_add (transform_kernel_integrable hR hF hw)
    (transform_kernel_integrable hR hG hw)]
  exact smul_add _ _ _

theorem transform_smul (c w : ℂ) (R : ℝ) (F : ℂ → ℂ) (d : ℂ) :
    transform c R (d • F) w = d • transform c R F w := by
  simp only [transform, Pi.smul_apply, smul_comm _ d, circleIntegral.integral_smul]

variable {N Q p : ℕ} {hQ : 0 < Q}

def transformLinear (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) {c w : ℂ} {R : ℝ}
    (hR : 0 < R) (hRc : R < c.im) (hw : w ∈ ball c R) (lam : ℂ) :
    space (radius a) →ₗ[ℂ] ℂ where
  toFun F := transform c R (formal A P a χ m lam F) w
  map_add' F G := by
    have he : formal A P a χ m lam (F + G) =
        formal A P a χ m lam F + formal A P a χ m lam G := by
      funext z
      simp only [← formalOperator_apply, map_add, Pi.add_apply]
    rw [he]
    exact transform_add hR.le (formal_circleIntegrable hN hp A P ha hae χ m lam F c hR hRc)
      (formal_circleIntegrable hN hp A P ha hae χ m lam G c hR hRc) hw
  map_smul' d F := by
    have he : formal A P a χ m lam (d • F) = d • formal A P a χ m lam F := by
      funext z
      simp only [← formalOperator_apply, map_smul, Pi.smul_apply]
    rw [he, transform_smul]
    rfl

theorem transform_chart_analytic (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) {c w : ℂ} {R : ℝ}
    (hR : 0 < R) (hRc : R < c.im) (hw : w ∈ ball c R)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set ℂ} (hU : IsOpen U) {J : ℂ → E →L[ℂ] space (radius a)}
    (hJ : AnalyticOnNhd ℂ J U) :
    AnalyticOnNhd ℂ (fun t : ℂ × E =>
      transform c R (formal A P a χ m t.1 (J t.1 t.2)) w) (U ×ˢ univ) := by
  apply FinitenessAllLevelAnalyticSubstitution.finite_linear_joint
    (fun lam => (transformLinear hN hp A P ha hae χ m hR hRc hw lam).comp (J lam).toLinearMap)
  intro v
  apply transform_curve_analytic hN hp A P ha hae χ m hR hRc hw hU
  intro z hz
  exact (FinitenessAllLevelAnalyticSubstitution.joint_analytic hJ (z, v)
    ⟨hz, mem_univ _⟩).comp (f := fun t : ℂ => (t, v)) (analyticAt_id.prod analyticAt_const)

/-- The exact global holomorphy conditions are scalar holomorphic
equations on the same Fredholm chart domain, for every test disk and point. -/
theorem equation_chart_analytic (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) {c w : ℂ} {R : ℝ}
    (hR : 0 < R) (hRc : R < c.im) (hw : w ∈ ball c R)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set ℂ} (hU : IsOpen U) {J : ℂ → E →L[ℂ] space (radius a)}
    (hJ : AnalyticOnNhd ℂ J U) :
    AnalyticOnNhd ℂ (fun t : ℂ × E =>
      transform c R (formal A P a χ m t.1 (J t.1 t.2)) w -
        formal A P a χ m t.1 (J t.1 t.2) w) (U ×ˢ univ) :=
  (transform_chart_analytic hN hp A P ha hae χ m hR hRc hw hU hJ).sub
    (FinitenessAllLevelAnalyticSubstitution.substitute_analytic hJ
      ((formal_joint_analytic A P a χ m w).mono (subset_univ _)))

#print axioms transformLinear
#print axioms transform_chart_analytic
#print axioms equation_chart_analytic

end FinitenessAllLevelCauchyConstraints
