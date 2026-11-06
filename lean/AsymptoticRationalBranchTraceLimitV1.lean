module

public import AsymptoticStripBranchReturnV1
public import AsymptoticOrbitBranchAlgebraV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open UpperHalfPlane MeasureTheory Filter Set AsymptoticStripCoordinates
open AsymptoticRegularTrace
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem indicator_coefficient_bound (S : Set ℍ) (a : ℍ → ℂ) {C : ℝ}
    (hC : 0≤C) (ha : ∀ z,‖a z‖≤C) (z : ℍ) : ‖S.indicator a z‖≤C := by
  by_cases hz : z∈S
  · simpa only [indicator_of_mem hz] using ha z
  · simpa only [indicator_of_notMem hz,norm_zero] using hC

/-- An individual rational branch has exactly the regular rooted trace
as its large-weight coefficient. Strip endpoints and rational freeness
supply the identity/nonidentity dichotomy; the actual slash phase is
retained throughout. The literal Fourier-mode action remains explicit. -/
theorem rational_branch_trace_tendsto {ε Y H C : ℝ}
    (hε : 0<ε) (hY : 0<Y) (hC : 0≤C)
    (g : AsymptoticRationalGroup.Group)
    (W : ℕ → AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (S : Set ℍ) (hS : MeasurableSet S) (hstrip : S⊆AsymptoticMassTransport.strip)
    [IsFiniteMeasure ((volume : Measure ℍ).restrict S)]
    (a : ℍ → ℂ) (hameas : Measurable a) (ha : ∀ z,‖a z‖≤C)
    (hend : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),g • z∈AsymptoticMassTransport.strip)
    (hregion : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),
      Y≤(g • z).im ∧ Y≤z.im ∧ (g • z).im≤H ∧ z.im≤H)
    (hact : ∀ h n, W h (liftedMode h n hε) =ᵐ[volume] S.indicator
      (fun z => (a z*AsymptoticSlashGauge.phase g (h+1) z) * (g • z).im *
        unitRepresentative (2*h) 0 n ε (cylinder (g • z)))) :
    Tendsto (fun h => liftedTrace h hε (W h)/(2*h+2:ℕ)) atTop
      (𝓝 (signedTrace volume (AsymptoticOrbitBranch.operator g (S.indicator a) hC
        (indicator_coefficient_bound S a hC ha))/(4*Real.pi))) := by
  let c := fun h z => a z*AsymptoticSlashGauge.phase g (h+1) z
  have hcmeas (h : ℕ) : AEStronglyMeasurable (c h) ((volume : Measure ℍ).restrict S) :=
    (hameas.mul (AsymptoticSlashGauge.phase_continuous g (h+1)).measurable).aestronglyMeasurable
  have hc (h : ℕ) : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),‖c h z‖≤C := by
    apply Eventually.of_forall
    intro z
    simpa only [c,norm_mul,AsymptoticSlashGauge.phase_norm,mul_one] using ha z
  have hepts : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),
      z∈AsymptoticMassTransport.strip ∧ g • z∈AsymptoticMassTransport.strip := by
    filter_upwards [ae_restrict_mem hS,hend] with z hz hg
    exact ⟨hstrip hz,hg⟩
  have hreg : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),
      Y≤(g • z).im ∧ Y≤z.im ∧ (g • z).im≤H ∧ z.im≤H ∧ |(g • z).re-z.re|≤1 := by
    filter_upwards [hregion,hepts] with z hz he
    refine ⟨hz.1,hz.2.1,hz.2.2.1,hz.2.2.2,?_⟩
    have hs₁ : 0≤z.re ∧ z.re<1 := he.1
    have hs₂ : 0≤(g • z).re ∧ (g • z).re<1 := he.2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  rw [AsymptoticOrbitBranch.operator_signedTrace]
  by_cases hg : g=1
  · rw [ite_eq_left hg]
    have hret : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),∃ n : ℤ,translate (g • z) n=z := by
      apply Eventually.of_forall
      intro z
      refine ⟨0,?_⟩
      simp only [hg,one_smul,translate,Int.cast_zero,add_zero]
    have hcoef : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),Tendsto (fun h => c h z) atTop (𝓝 (a z)) := by
      apply Eventually.of_forall
      intro z
      simpa only [c,hg,AsymptoticSlashGauge.phase_one,mul_one] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => a z) atTop (𝓝 (a z)))
    have ht := returning_branch_trace_tendsto hε hY hC W S hS hstrip
      (fun z => g • z) (AsymptoticRationalBranches.action_continuous g).measurable
      c a hcmeas hc hreg hret hcoef hact
    have hi : Integrable a ((volume : Measure ℍ).restrict S) :=
      (integrable_const C).mono' hameas.aestronglyMeasurable (Eventually.of_forall ha)
    have he : (∫ z : ℍ,(S.indicator a z).re)= (∫ z in S,a z).re := by
      have hind : (fun z => (S.indicator a z).re)=S.indicator (fun z => (a z).re) := by
        funext z
        by_cases hz : z∈S <;> simp [hz]
      rw [hind,integral_indicator hS]
      exact integral_re hi
    rw [he]
    exact ht
  · rw [ite_eq_right hg,zero_div]
    have ho := nonreturning_branch_trace_isLittleO hε hY hC W S hS hstrip
      (fun z => g • z) (AsymptoticRationalBranches.action_continuous g).measurable
      c hcmeas hc hreg (ae_nonidentity_strip_nonreturn g hg S hepts) hact
    exact ho.tendsto_div_nhds_zero

#print axioms indicator_coefficient_bound
#print axioms rational_branch_trace_tendsto

end AsymptoticUnweightedKernel
