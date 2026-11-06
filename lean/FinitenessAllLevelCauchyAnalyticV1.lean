module

public import FinitenessAllLevelCauchyConstraintsV1
public import FinitenessAllLevelChartTestsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCauchyConstraints

open Complex Metric Set Filter MeasureTheory FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelGlobalHeight
  FinitenessAllLevelFormalContinuation QuantitativeArithmeticRetainedCertificate
open scoped Topology

def kernel (c w : ℂ) (R : ℝ) (θ : ℝ) : ℂ :=
  (circleMap 0 R θ * I) * (circleMap c R θ - w)⁻¹

theorem kernel_measurable (c w : ℂ) (R : ℝ) : Measurable (kernel c w R) :=
  ((continuous_circleMap 0 R).measurable.mul_const I).mul
    (((continuous_circleMap c R).measurable.sub_const w).inv)

theorem kernel_bound {c w : ℂ} {R : ℝ} (hR : 0 < R) (hw : w ∈ ball c R) (θ : ℝ) :
    ‖kernel c w R θ‖ ≤ R / (R - dist w c) := by
  have hgap : 0 < R - dist w c := sub_pos.mpr (mem_ball.mp hw)
  have hl : R - dist w c ≤ ‖circleMap c R θ - w‖ := by
    have hc : dist (circleMap c R θ) c = R := mem_sphere.mp (circleMap_mem_sphere c hR.le θ)
    have ht := dist_triangle (circleMap c R θ) w c
    rw [hc, dist_eq_norm (circleMap c R θ) w] at ht
    linarith
  simp only [kernel, norm_mul, norm_inv, norm_I, mul_one, norm_circleMap_zero, abs_of_pos hR]
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hR.le hgap hl

variable {N Q p : ℕ} {hQ : 0 < Q}

/-- Cauchy tests of the genuine finite reconstruction are holomorphic
after substitution of an analytic disk input, on its original common domain. -/
theorem transform_curve_analytic (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) {c w : ℂ} {R : ℝ}
    (hR : 0 < R) (hRc : R < c.im) (hw : w ∈ ball c R)
    {U : Set ℂ} (hU : IsOpen U) {F : ℂ → space (radius a)} (hF : AnalyticOnNhd ℂ F U) :
    AnalyticOnNhd ℂ (fun lam => transform c R (formal A P a χ m lam (F lam)) w) U := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  let H : ℂ → ℝ → ℂ := fun lam θ => kernel c w R θ *
    formal A P a χ m lam (F lam) (circleMap c R θ)
  have he (lam : ℂ) : transform c R (formal A P a χ m lam (F lam)) w =
      (2 * Real.pi * I : ℂ)⁻¹ * ∫ θ, H lam θ ∂μ := by
    simp only [transform, circleIntegral, smul_eq_mul, deriv_circleMap,
      intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity), μ, H,
      kernel, mul_assoc]
  have hi : AnalyticOnNhd ℂ (fun lam => ∫ θ, H lam θ ∂μ) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro v hv
    have hn : ∀ᶠ t in 𝓝 v, t ∈ U ∧ ‖F t‖ < ‖F v‖ + 1 :=
      (show ∀ᶠ t in 𝓝 v, t ∈ U from hU.mem_nhds hv).and
        ((hF v hv).continuousAt.norm.eventually_lt_const (lt_add_one _))
    obtain ⟨r, hr, hnear⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
    obtain ⟨C, hC, hb⟩ := formal_uniform_bound hN hp A P ha hae χ m
      (B := ‖v‖ + r) (by positivity) (sub_pos.mpr hRc)
    let D := (R / (R - dist w c)) * (C * (‖F v‖ + 1))
    have hm (lam : ℂ) : Measurable (H lam) :=
      (kernel_measurable c w R).mul ((formal_measurable A P a χ m lam (F lam)).comp
        (continuous_circleMap c R).measurable)
    apply DifferentiableAt.differentiableWithinAt
    refine FinitenessAllLevelAnalyticIntegral.differentiableAt_integral_local
      μ H hm (half_pos hr) ?_ (integrable_const D) ?_
    · intro θ t ht
      have ht' : t ∈ closedBall v r := by
        simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using ht
      have hh := (formal_joint_analytic A P a χ m (circleMap c R θ)
        (t, F t) (mem_univ _)).comp (f := fun s : ℂ => (s, F s))
        (analyticAt_id.prod (hF t (hnear ht').1))
      exact (analyticAt_const.mul hh).differentiableAt
    · apply Filter.Eventually.of_forall
      intro θ t ht
      have ht' : t ∈ closedBall v r := by
        simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using ht
      have hl : ‖t‖ ≤ ‖v‖ + r := by
        have hd := mem_closedBall.mp ht'
        calc
          ‖t‖ ≤ ‖t - v‖ + ‖v‖ := norm_le_norm_sub_add _ _
          _ ≤ ‖v‖ + r := by rw [← dist_eq_norm] at *; linarith
      have hf : ‖formal A P a χ m t (F t) (circleMap c R θ)‖ ≤ C * (‖F v‖ + 1) :=
        (hb t hl (F t) _ (height_lower
          (sphere_subset_closedBall (circleMap_mem_sphere c hR.le θ)))).trans
          (mul_le_mul_of_nonneg_left (hnear ht').2.le hC)
      dsimp only [H, D]
      rw [norm_mul]
      exact mul_le_mul (kernel_bound hR hw θ) hf (norm_nonneg _)
        (div_nonneg hR.le (sub_pos.mpr (mem_ball.mp hw)).le)
  have hef : (fun lam => transform c R (formal A P a χ m lam (F lam)) w) =
      fun lam => (2 * Real.pi * I : ℂ)⁻¹ * ∫ θ, H lam θ ∂μ := funext he
  rw [hef]
  exact analyticOnNhd_const.mul hi

#print axioms kernel_bound
#print axioms transform_curve_analytic

end FinitenessAllLevelCauchyConstraints
