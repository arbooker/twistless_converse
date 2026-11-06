module

public import AsymptoticNonreturningBranchTraceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open UpperHalfPlane Filter MeasureTheory Set AsymptoticBergmanDecay AsymptoticStripCoordinates
open scoped Topology

/-- A returning branch contributes its limiting coefficient. The full
integer periodization, rather than a truncated kernel, is used. -/
theorem returning_integral_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (z u : α → ℍ)
    (hz : Measurable z) (hu : Measurable u) (c : ℕ → α → ℂ) (a : α → ℂ)
    (hcmeas : ∀ h, AEStronglyMeasurable (c h) μ)
    {Y H R C : ℝ} (hY : 0<Y) (hC : 0≤C)
    (hc : ∀ h, ∀ᵐ x ∂μ, ‖c h x‖≤C)
    (hregion : ∀ᵐ x ∂μ, Y≤(z x).im ∧ Y≤(u x).im ∧ (z x).im≤H ∧
      (u x).im≤H ∧ |(z x).re-(u x).re|≤R)
    (hreturn : ∀ᵐ x ∂μ, ∃ n : ℤ, translate (z x) n=u x)
    (hcoef : ∀ᵐ x ∂μ, Tendsto (fun h => c h x) atTop (𝓝 (a x))) :
    Tendsto (fun h : ℕ => ∫ x, c h x *
      (∑' n : ℤ, base (translate (z x) n) (u x)^(2*h+2)) ∂μ) atTop (𝓝 (∫ x,a x ∂μ)) := by
  let D := compactKernelBound Y H R
  have hmeas (h : ℕ) : AEStronglyMeasurable (fun x => c h x *
      (∑' n : ℤ, base (translate (z x) n) (u x)^(2*h+2))) μ :=
    (hcmeas h).mul ((periodized_kernel_measurable h z u hz hu).aestronglyMeasurable)
  have hbound (h : ℕ) : ∀ᵐ x ∂μ, ‖c h x *
      (∑' n : ℤ, base (translate (z x) n) (u x)^(2*h+2))‖≤C*D := by
    filter_upwards [hc h,hregion] with x hcx hx
    rw [norm_mul]
    exact mul_le_mul hcx
      (periodized_kernel_norm_bound h hY (z x) (u x) hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2)
      (norm_nonneg _) hC
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun h : ℕ => c h x *
      (∑' n : ℤ, base (translate (z x) n) (u x)^(2*h+2))) atTop (𝓝 (a x)) := by
    filter_upwards [hreturn,hcoef] with x hx hax
    have hk := periodized_kernel_tendsto (z x) (u x)
    have hr : returnValue (z x) (u x)=1 := by
      classical
      exact ite_eq_left hx
    rw [hr] at hk
    simpa only [mul_one] using hax.mul hk
  exact tendsto_integral_of_dominated_convergence
    (fun _ : α => C*D) hmeas (integrable_const _) hbound hlim

/-- The actual Fourier trace of a returning branch has leading term
k/(4π) times the integral of its limiting coefficient. -/
theorem returning_branch_trace_tendsto {ε Y H R C : ℝ}
    (hε : 0<ε) (hY : 0<Y) (hC : 0≤C)
    (W : ℕ → AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (S : Set ℍ) (hS : MeasurableSet S) (hstrip : S⊆AsymptoticMassTransport.strip)
    [IsFiniteMeasure ((volume : Measure ℍ).restrict S)]
    (u : ℍ → ℍ) (hu : Measurable u) (c : ℕ → ℍ → ℂ) (a : ℍ → ℂ)
    (hcmeas : ∀ h, AEStronglyMeasurable (c h) ((volume : Measure ℍ).restrict S))
    (hc : ∀ h, ∀ᵐ z ∂((volume : Measure ℍ).restrict S), ‖c h z‖≤C)
    (hregion : ∀ᵐ z ∂((volume : Measure ℍ).restrict S), Y≤(u z).im ∧ Y≤z.im ∧
      (u z).im≤H ∧ z.im≤H ∧ |(u z).re-z.re|≤R)
    (hreturn : ∀ᵐ z ∂((volume : Measure ℍ).restrict S), ∃ n : ℤ, translate (u z) n=z)
    (hcoef : ∀ᵐ z ∂((volume : Measure ℍ).restrict S), Tendsto (fun h => c h z) atTop (𝓝 (a z)))
    (hact : ∀ h n, W h (liftedMode h n hε) =ᵐ[volume] S.indicator
      (fun z => c h z * (u z).im * unitRepresentative (2*h) 0 n ε (cylinder (u z)))) :
    Tendsto (fun h => liftedTrace h hε (W h)/(2*h+2:ℕ)) atTop
      (𝓝 ((∫ z in S,a z).re/(4*Real.pi))) := by
  have hi := returning_integral_tendsto u id hu measurable_id c a hcmeas hY hC hc hregion hreturn hcoef
  have hre := Complex.continuous_re.tendsto _ |>.comp hi
  have hr : Tendsto (fun h : ℕ => ((2*h+1:ℕ):ℝ)/((2*h+2:ℕ):ℝ)) atTop (𝓝 1) := by
    simpa only [norm_div,Complex.norm_natCast,norm_one] using weight_ratio_tendsto.norm
  have ht := (hr.div_const (4*Real.pi)).mul hre
  rw [one_div_mul_eq_div] at ht
  apply ht.congr
  intro h
  dsimp only [Function.comp_apply,id]
  have hreg : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),
      Y≤(u z).im ∧ Y≤z.im ∧ (u z).im≤H ∧ z.im≤H :=
    hregion.mono (fun _ hz => ⟨hz.1,hz.2.1,hz.2.2.1,hz.2.2.2.1⟩)
  rw [branch_trace_periodized h hε hY hC (W h) S hS hstrip u hu (c h) (hcmeas h) (hc h) hreg (hact h)]
  ring

#print axioms returning_integral_tendsto
#print axioms returning_branch_trace_tendsto

end AsymptoticUnweightedKernel
