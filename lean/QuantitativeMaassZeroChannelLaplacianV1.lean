module

public import QuantitativeMaassZeroFourierDifferentialV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

namespace QuantitativeMaass

/-- Local positive-height version; no smooth extension through y=0 is
required of an automorphic function. -/
theorem hasDerivAt_zeroFourier_positive (F Fy : ℝ → ℝ → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Ioi (0:ℝ)))
    (hFy : ContinuousOn (Function.uncurry Fy) (univ ×ˢ Ioi (0:ℝ)))
    (hd : ∀ x y, 0<y → HasDerivAt (F x) (Fy x y) y)
    (y : ℝ) (hy : 0<y) : HasDerivAt (zeroFourier F) (zeroFourier Fy y) y := by
  have hs : Ioo (y/2) (3*y/2) ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
  have hrect : Icc (0:ℝ) 1 ×ˢ Icc (y/2) (3*y/2) ⊆ univ ×ˢ Ioi (0:ℝ) := by
    intro z hz
    refine ⟨mem_univ _,?_⟩
    change 0<z.2
    have hlo : y/2≤z.2 := hz.2.1
    linarith
  obtain ⟨K,hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hFy.mono hrect)
  have hc (v : ℝ) (hv : 0<v) : Continuous (fun x => F x v) :=
    hF.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _,hv⟩)
  have hdc (v : ℝ) (hv : 0<v) : Continuous (fun x => Fy x v) :=
    hFy.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _,hv⟩)
  have hmeas : ∀ᶠ v in 𝓝 y, AEStronglyMeasurable (fun x => F x v)
      (volume.restrict (Ι (0:ℝ) 1)) := by
    filter_upwards [hs] with v hv
    exact (hc v (by linarith [hv.1])).aestronglyMeasurable
  have hi := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v x => F x v) (F' := fun v x => Fy x v)
    (μ := volume) (a := (0:ℝ)) (b := 1) (bound := fun _ => K)
    hs hmeas ((hc y hy).intervalIntegrable _ _) (hdc y hy).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x hx v hv => hK (x,v)
      ⟨⟨(show 0<x from (by simpa using hx.1)).le,by simpa using hx.2⟩,
        ⟨hv.1.le,hv.2.le⟩⟩)
    (continuous_const.intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun x _ v hv => hd x v (by linarith [hv.1]))
  exact hi.2

theorem zeroFourier_secondVertical_positive (F Fy Fyy : ℝ → ℝ → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Ioi (0:ℝ)))
    (hFy : ContinuousOn (Function.uncurry Fy) (univ ×ˢ Ioi (0:ℝ)))
    (hFyy : ContinuousOn (Function.uncurry Fyy) (univ ×ˢ Ioi (0:ℝ)))
    (hd : ∀ x y, 0<y → HasDerivAt (F x) (Fy x y) y)
    (hdd : ∀ x y, 0<y → HasDerivAt (Fy x) (Fyy x y) y)
    (y : ℝ) (hy : 0<y) : deriv (deriv (zeroFourier F)) y=zeroFourier Fyy y := by
  have he : deriv (zeroFourier F) =ᶠ[𝓝 y] zeroFourier Fy := by
    filter_upwards [Ioi_mem_nhds hy] with v hv
    exact (hasDerivAt_zeroFourier_positive F Fy hF hFy hd v hv).deriv
  rw [he.deriv_eq]
  exact (hasDerivAt_zeroFourier_positive Fy Fyy hFy hFyy hdd y hy).deriv

/-- The literal hyperbolic Laplacian in Cartesian coordinates. -/
def cartesianLaplacian (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  -(y:ℂ)^2*(deriv (deriv (fun v => F v y)) x+deriv (deriv (F x)) y)

/-- Exact zero-channel intertwining of the actual differential expression.
The x-boundary terms cancel by periodicity, while the vertical derivatives
pass through the compact horocycle integral by the proved local theorem. -/
theorem zeroFourier_cartesianLaplacian (F Fy Fyy : ℝ → ℝ → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Ioi (0:ℝ)))
    (hFy : ContinuousOn (Function.uncurry Fy) (univ ×ˢ Ioi (0:ℝ)))
    (hFyy : ContinuousOn (Function.uncurry Fyy) (univ ×ˢ Ioi (0:ℝ)))
    (hd : ∀ x y, 0<y → HasDerivAt (F x) (Fy x y) y)
    (hdd : ∀ x y, 0<y → HasDerivAt (Fy x) (Fyy x y) y)
    (hperiod : ∀ y, 0<y → Function.Periodic (fun x => F x y) 1)
    (hxx : ∀ y, 0<y → Differentiable ℝ (deriv (fun x => F x y)))
    (hxxc : ∀ y, 0<y → Continuous (deriv (deriv (fun x => F x y))))
    (y : ℝ) (hy : 0<y) :
    zeroFourier (cartesianLaplacian F) y=-(y:ℂ)^2*deriv (deriv (zeroFourier F)) y := by
  have hyy (x : ℝ) : deriv (deriv (F x)) y=Fyy x y := by
    have he : deriv (F x) =ᶠ[𝓝 y] Fy x := by
      filter_upwards [Ioi_mem_nhds hy] with v hv
      exact (hd x v hv).deriv
    rw [he.deriv_eq]
    exact (hdd x y hy).deriv
  have hcont : Continuous (fun x => Fyy x y) :=
    hFyy.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _,hy⟩)
  unfold zeroFourier cartesianLaplacian
  simp_rw [hyy]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hxxc y hy).intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
    periodic_secondDerivative_average_zero _ (hperiod y hy) (hxx y hy) (hxxc y hy),zero_add]
  exact congrArg (fun z : ℂ => -(y:ℂ)^2*z)
    (zeroFourier_secondVertical_positive F Fy Fyy hF hFy hFyy hd hdd y hy).symm

#print axioms hasDerivAt_zeroFourier_positive
#print axioms zeroFourier_cartesianLaplacian

end QuantitativeMaass
