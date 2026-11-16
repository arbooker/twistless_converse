module

public import QuantitativeMaassHalfDensityGeneratorV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

namespace QuantitativeMaass

/-- The actual differential expression in a width-w cusp coordinate x↦w*x.
Only the horizontal second derivative receives the factor w⁻². -/
def periodLaplacian (w : ℝ) (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  -(y:ℂ)^2*((w:ℂ)⁻¹^2*deriv (deriv (fun v => F v y)) x+
    deriv (deriv (F x)) y)

/-- Averaging the width-correct differential expression removes its
horizontal part exactly, for every width. -/
theorem zeroFourier_periodLaplacian (w : ℝ) (F Fy Fyy : ℝ → ℝ → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Ioi (0:ℝ)))
    (hFy : ContinuousOn (Function.uncurry Fy) (univ ×ˢ Ioi (0:ℝ)))
    (hFyy : ContinuousOn (Function.uncurry Fyy) (univ ×ˢ Ioi (0:ℝ)))
    (hd : ∀ x y, 0<y → HasDerivAt (F x) (Fy x y) y)
    (hdd : ∀ x y, 0<y → HasDerivAt (Fy x) (Fyy x y) y)
    (hperiod : ∀ y, 0<y → Function.Periodic (fun x => F x y) 1)
    (hxx : ∀ y, 0<y → Differentiable ℝ (deriv (fun x => F x y)))
    (hxxc : ∀ y, 0<y → Continuous (deriv (deriv (fun x => F x y))))
    (y : ℝ) (hy : 0<y) :
    zeroFourier (periodLaplacian w F) y=-(y:ℂ)^2*deriv (deriv (zeroFourier F)) y := by
  have hyy (x : ℝ) : deriv (deriv (F x)) y=Fyy x y := by
    have he : deriv (F x) =ᶠ[𝓝 y] Fy x := by
      filter_upwards [Ioi_mem_nhds hy] with v hv
      exact (hd x v hv).deriv
    rw [he.deriv_eq]
    exact (hdd x y hy).deriv
  have hcont : Continuous (fun x => Fyy x y) :=
    hFyy.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _,hy⟩)
  have hxc : Continuous (fun x => (w:ℂ)⁻¹^2*deriv (deriv (fun v => F v y)) x) :=
    continuous_const.mul (hxxc y hy)
  unfold zeroFourier periodLaplacian
  simp_rw [hyy]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hxc.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,
    periodic_secondDerivative_average_zero _ (hperiod y hy) (hxx y hy) (hxxc y hy),mul_zero,zero_add]
  exact congrArg (fun z : ℂ => -(y:ℂ)^2*z)
    (zeroFourier_secondVertical_positive F Fy Fyy hF hFy hFyy hd hdd y hy).symm


#print axioms zeroFourier_periodLaplacian

end QuantitativeMaass
