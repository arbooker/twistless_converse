module

public import FinitenessAllLevelAnalyticIntegralV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelAnalyticIntegral

open Complex Metric Set Filter MeasureTheory FinitenessAllLevelMeasurableDerivative
open scoped Topology

/-- The local version permits the analytic Fredholm lift to be defined
only on its actual parameter neighborhood. -/
theorem differentiableAt_integral_local {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (H : ℂ → α → ℂ) (hH : ∀ v, Measurable (H v))
    {w : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ∀ z, ∀ v ∈ closedBall w (2 * r), DifferentiableAt ℂ (fun t => H t z) v)
    {b : α → ℝ} (hbi : Integrable b μ)
    (hb : ∀ᵐ z ∂μ, ∀ v ∈ closedBall w (2 * r), ‖H v z‖ ≤ b z) :
    DifferentiableAt ℂ (fun v => ∫ z, H v z ∂μ) w := by
  have hw : w ∈ closedBall w (2 * r) := mem_closedBall_self (by positivity)
  have hi : Integrable (H w) μ := hbi.mono' (hH w).aestronglyMeasurable
    (hb.mono (fun z hz => hz w hw))
  have hdm : AEStronglyMeasurable (fun z => deriv (fun v => H v z) w) μ :=
    (measurable_derivative H hH w (fun z => hd z w hw)).aestronglyMeasurable
  have hsub {v : ℂ} (hv : v ∈ ball w r) : closedBall v r ⊆ closedBall w (2 * r) := by
    intro t ht
    apply mem_closedBall.mpr
    have ht' := mem_closedBall.mp ht
    have hv' := mem_ball.mp hv
    calc
      dist t w ≤ dist t v + dist v w := dist_triangle _ _ _
      _ ≤ 2 * r := by linarith
  have hdb : ∀ᵐ z ∂μ, ∀ v ∈ ball w r, ‖deriv (fun t => H t z) v‖ ≤ b z / r := by
    apply hb.mono
    intro z hz v hv
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    · apply DifferentiableOn.diffContOnCl
      rw [closure_ball v hr.ne']
      exact fun t ht => (hd z t (hsub hv ht)).differentiableWithinAt
    · intro t ht
      exact hz t (hsub hv (sphere_subset_closedBall ht))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds w hr)
    (Filter.Eventually.of_forall (fun v => (hH v).aestronglyMeasurable)) hi hdm hdb
    (hbi.div_const r) (Filter.Eventually.of_forall (fun z v hv =>
      (hd z v (hsub hv (mem_closedBall_self hr.le))).hasDerivAt))).2.differentiableAt

#print axioms differentiableAt_integral_local

end FinitenessAllLevelAnalyticIntegral
