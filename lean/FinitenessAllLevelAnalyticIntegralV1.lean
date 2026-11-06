module

public import FinitenessAllLevelMeasurableDerivativeV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelAnalyticIntegral

open Complex Metric Set Filter MeasureTheory FinitenessAllLevelMeasurableDerivative
open scoped Topology

/-- A measurable entire family with locally uniform integrable majorants
has an entire integral. The majorant is chosen on a common parameter disk. -/
theorem differentiable_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (H : ℂ → α → ℂ) (hH : ∀ w, Measurable (H w))
    (hd : ∀ z, Differentiable ℂ (fun w => H w z))
    (hb : ∀ w : ℂ, ∃ b : α → ℝ, Integrable b μ ∧
      ∀ᵐ z ∂μ, ∀ v ∈ closedBall w 2, ‖H v z‖ ≤ b z) :
    Differentiable ℂ (fun w => ∫ z, H w z ∂μ) := by
  intro w
  obtain ⟨b, hbi, hbound⟩ := hb w
  have hi : Integrable (H w) μ := hbi.mono' (hH w).aestronglyMeasurable
    (hbound.mono (fun z hz => hz w (mem_closedBall_self (by norm_num))))
  have hdm : AEStronglyMeasurable (fun z => deriv (fun v => H v z) w) μ :=
    (measurable_derivative H hH w (fun z => hd z w)).aestronglyMeasurable
  have hdb : ∀ᵐ z ∂μ, ∀ v ∈ ball w 1, ‖deriv (fun t => H t z) v‖ ≤ b z := by
    apply hbound.mono
    intro z hz v hv
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (f := fun t => H t z) (c := v) (R := 1) (by norm_num)
      (hd z).diffContOnCl (fun t ht => hz t (by
        apply mem_closedBall.mpr
        have ht' : dist t v = 1 := mem_sphere.mp ht
        have hv' : dist v w < 1 := mem_ball.mp hv
        calc
          dist t w ≤ dist t v + dist v w := dist_triangle _ _ _
          _ ≤ 2 := by linarith))
    simpa only [div_one] using hc
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds w (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall (fun v => (hH v).aestronglyMeasurable)) hi hdm hdb hbi
    (Filter.Eventually.of_forall (fun z v _ => (hd z v).hasDerivAt))).2.differentiableAt

theorem analytic_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (H : ℂ → α → ℂ) (hH : ∀ w, Measurable (H w))
    (hd : ∀ z, Differentiable ℂ (fun w => H w z))
    (hb : ∀ w : ℂ, ∃ b : α → ℝ, Integrable b μ ∧
      ∀ᵐ z ∂μ, ∀ v ∈ closedBall w 2, ‖H v z‖ ≤ b z) :
    AnalyticOnNhd ℂ (fun w => ∫ z, H w z ∂μ) univ :=
  DifferentiableOn.analyticOnNhd (differentiable_integral μ H hH hd hb).differentiableOn isOpen_univ

#print axioms differentiable_integral
#print axioms analytic_integral

end FinitenessAllLevelAnalyticIntegral
