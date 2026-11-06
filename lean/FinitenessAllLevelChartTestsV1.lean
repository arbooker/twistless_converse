module

public import FinitenessAllLevelFormalTestsV1
public import FinitenessAllLevelLocalAnalyticIntegralV1
public import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex Metric Set Filter MeasureTheory FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelGlobalHeight
  QuantitativeArithmeticRetainedCertificate
open scoped Topology

variable {N Q p : ℕ} {hQ : 0 < Q}

/-- A holomorphically varying disk input may be substituted before testing.
All tests retain the same open parameter domain. -/
theorem test_curve_analytic (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (μ : Measure ℂ) {ψ : ℂ → ℂ}
    (hψm : Measurable ψ) (hψ : Integrable ψ μ)
    {y : ℝ} (hy : 0 < y) (hs : ∀ z, ψ z ≠ 0 → y ≤ z.im)
    {U : Set ℂ} (hU : IsOpen U) {F : ℂ → space (radius a)} (hF : AnalyticOnNhd ℂ F U) :
    AnalyticOnNhd ℂ (fun lam => ∫ z, ψ z * formal A P a χ m lam (F lam) z ∂μ) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro w hw
  have hn : ∀ᶠ v in 𝓝 w, v ∈ U ∧ ‖F v‖ < ‖F w‖ + 1 :=
    (show ∀ᶠ v in 𝓝 w, v ∈ U from hU.mem_nhds hw).and ((hF w hw).continuousAt.norm.eventually_lt_const (lt_add_one _))
  obtain ⟨r, hr, hnear⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
  obtain ⟨C, hC, hb⟩ := formal_uniform_bound hN hp A P ha hae χ m
    (B := ‖w‖ + r) (by positivity) hy
  apply DifferentiableAt.differentiableWithinAt
  refine FinitenessAllLevelAnalyticIntegral.differentiableAt_integral_local
    (r := r / 2) (b := fun z => (C * (‖F w‖ + 1)) * ‖ψ z‖) μ
    (fun v z => ψ z * formal A P a χ m v (F v) z)
    (fun v => hψm.mul (formal_measurable A P a χ m v (F v)))
    (half_pos hr) ?_ (hψ.norm.const_mul _) ?_
  · intro z v hv
    have hv' : v ∈ closedBall w r := by simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hv
    have hh := (formal_joint_analytic A P a χ m z (v, F v) (mem_univ _)).comp
      (f := fun t : ℂ => (t, F t)) (analyticAt_id.prod (hF v (hnear hv').1))
    exact ((analyticAt_const.mul hh).differentiableAt)
  · apply Filter.Eventually.of_forall
    intro z v hv
    by_cases hz : ψ z = 0
    · simp only [hz, zero_mul, norm_zero, mul_zero, le_refl]
    · have hv' : v ∈ closedBall w r := by
        simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hv
      have hl : ‖v‖ ≤ ‖w‖ + r := by
        have hd := mem_closedBall.mp hv'
        calc
          ‖v‖ ≤ ‖v - w‖ + ‖w‖ := norm_le_norm_sub_add _ _
          _ ≤ ‖w‖ + r := by rw [← dist_eq_norm] at *; linarith
      have hf : ‖formal A P a χ m v (F v) z‖ ≤ C * (‖F w‖ + 1) :=
        (hb v hl (F v) z (hs z hz)).trans
          (mul_le_mul_of_nonneg_left (hnear hv').2.le hC)
      rw [norm_mul, mul_comm (C * (‖F w‖ + 1))]
      exact mul_le_mul_of_nonneg_left hf (norm_nonneg _)

end FinitenessAllLevelFormalContinuation

namespace FinitenessAllLevelAnalyticSubstitution

open Set

/-- For finite-dimensional linear input, scalar analyticity on each fixed
vector gives joint analyticity on the same product domain. -/
theorem finite_linear_joint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set ℂ} (T : ℂ → E →ₗ[ℂ] ℂ)
    (hT : ∀ v, AnalyticOnNhd ℂ (fun w => T w v) U) :
    AnalyticOnNhd ℂ (fun t : ℂ × E => T t.1 t.2) (U ×ˢ univ) := by
  let b := Module.finBasis ℂ E
  have he (w : ℂ) (v : E) : T w v = ∑ i, b.repr v i * T w (b i) := by
    calc
      _ = T w (∑ i, b.repr v i • b i) := congrArg (T w) (b.sum_repr v).symm
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  have hef : (fun t : ℂ × E => T t.1 t.2) =
      fun t : ℂ × E => ∑ i, b.repr t.2 i * T t.1 (b i) := funext (fun t => he t.1 t.2)
  rw [hef]
  intro t ht
  apply Finset.analyticAt_fun_sum
  intro i _
  have hc : AnalyticAt ℂ (fun v : E => b.repr v i) t.2 :=
    (b.coord i).toContinuousLinearMap.analyticAt _
  exact (hc.comp ((ContinuousLinearMap.snd ℂ ℂ E).analyticAt t)).mul
    ((hT (b i) t.1 ht.1).comp ((ContinuousLinearMap.fst ℂ ℂ E).analyticAt t))

end FinitenessAllLevelAnalyticSubstitution

namespace FinitenessAllLevelFormalContinuation

open Set MeasureTheory FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}

/-- The actual integral constraints after Fredholm substitution are
holomorphic on one common finite-dimensional neighborhood. -/
theorem chart_test_analytic (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (μ : Measure ℂ) {ψ : ℂ → ℂ}
    (hψm : Measurable ψ) (hψ : Integrable ψ μ)
    {y : ℝ} (hy : 0 < y) (hs : ∀ z, ψ z ≠ 0 → y ≤ z.im)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set ℂ} (hU : IsOpen U) {J : ℂ → E →L[ℂ] space (radius a)}
    (hJ : AnalyticOnNhd ℂ J U) :
    AnalyticOnNhd ℂ (fun t : ℂ × E =>
      ∫ z, ψ z * formal A P a χ m t.1 (J t.1 t.2) z ∂μ) (U ×ˢ univ) := by
  apply FinitenessAllLevelAnalyticSubstitution.finite_linear_joint
    (fun lam => (testLinear hN hp A P ha hae χ m μ hψ hy hs lam).comp (J lam).toLinearMap)
  intro v
  apply test_curve_analytic hN hp A P ha hae χ m μ hψm hψ hy hs hU
  intro w hw
  exact (FinitenessAllLevelAnalyticSubstitution.joint_analytic hJ (w, v)
    ⟨hw, mem_univ _⟩).comp (f := fun t : ℂ => (t, v))
      (show AnalyticAt ℂ (fun t : ℂ => (t, v)) w from analyticAt_id.prod analyticAt_const)

#print axioms test_curve_analytic
#print axioms FinitenessAllLevelAnalyticSubstitution.finite_linear_joint
#print axioms chart_test_analytic

end FinitenessAllLevelFormalContinuation
