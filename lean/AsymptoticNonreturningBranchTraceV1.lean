module

public import AsymptoticBranchKernelTraceV1
public import AsymptoticPeriodizedKernelIntegralV1
public import AsymptoticNormalizedKernelLimitV1
public import Mathlib.Analysis.Asymptotics.Lemmas

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open MeasureTheory UpperHalfPlane Set Filter AsymptoticStripCoordinates
open AsymptoticBergmanDecay
open scoped Topology

theorem branch_trace_periodized (h : ℕ) {ε Y H C : ℝ} (hε : 0 < ε) (hY : 0 < Y) (hC : 0 ≤ C)
    (W : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (S : Set ℍ) (hS : MeasurableSet S) (hstrip : S ⊆ AsymptoticMassTransport.strip)
    [IsFiniteMeasure ((volume : Measure ℍ).restrict S)]
    (u : ℍ → ℍ) (hu : Measurable u) (c : ℍ → ℂ)
    (hcmeas : AEStronglyMeasurable c ((volume : Measure ℍ).restrict S))
    (hc : ∀ᵐ z ∂((volume : Measure ℍ).restrict S), ‖c z‖ ≤ C)
    (hregion : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),
      Y ≤ (u z).im ∧ Y ≤ z.im ∧ (u z).im ≤ H ∧ z.im ≤ H)
    (hact : ∀ n, W (liftedMode h n hε) =ᵐ[volume] S.indicator
      (fun z => c z * (u z).im * unitRepresentative (2*h) 0 n ε (cylinder (u z)))) :
    liftedTrace h hε W = ((2*h+1 : ℕ) : ℝ)/(4*Real.pi) *
      (∫ z in S, c z * (∑' n : ℤ, base (translate (u z) n) z^(2*h+2))).re := by
  rw [branch_trace_integral h hε hY hC W S hS hstrip u hu c hcmeas hc hregion hact]
  have hi : (∫ z in S, c z * ((u z).im*z.im : ℝ) * fourierKernel h ε (u z) z) =
      (((2*h+1 : ℕ) : ℂ)/(4*Real.pi)) *
        ∫ z in S, c z * (∑' n : ℤ, base (translate (u z) n) z^(2*h+2)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [mul_assoc, hyperbolicKernel_periodization h hε (u z) z]
    ring
  rw [hi]
  have hcoef : ((2*h+1 : ℕ) : ℂ)/(4*Real.pi) =
      ((((2*h+1 : ℕ) : ℝ)/(4*Real.pi) : ℝ) : ℂ) := by norm_cast
  rw [hcoef, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- A nonreturning measurable branch has o(k) trace in the actual
unweighted Fourier compression. Its bounded coefficient may vary with
the weight, so the theorem includes the slash phases of rational words. -/
theorem nonreturning_branch_trace_isLittleO {ε Y H R C : ℝ}
    (hε : 0 < ε) (hY : 0 < Y) (hC : 0 ≤ C)
    (W : ℕ → AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (S : Set ℍ) (hS : MeasurableSet S) (hstrip : S ⊆ AsymptoticMassTransport.strip)
    [IsFiniteMeasure ((volume : Measure ℍ).restrict S)]
    (u : ℍ → ℍ) (hu : Measurable u) (c : ℕ → ℍ → ℂ)
    (hcmeas : ∀ h, AEStronglyMeasurable (c h) ((volume : Measure ℍ).restrict S))
    (hc : ∀ h, ∀ᵐ z ∂((volume : Measure ℍ).restrict S), ‖c h z‖ ≤ C)
    (hregion : ∀ᵐ z ∂((volume : Measure ℍ).restrict S), Y ≤ (u z).im ∧ Y ≤ z.im ∧
      (u z).im ≤ H ∧ z.im ≤ H ∧ |(u z).re-z.re| ≤ R)
    (hne : ∀ᵐ z ∂((volume : Measure ℍ).restrict S), ∀ n : ℤ, translate (u z) n ≠ z)
    (hact : ∀ h n, W h (liftedMode h n hε) =ᵐ[volume] S.indicator
      (fun z => c h z * (u z).im * unitRepresentative (2*h) 0 n ε (cylinder (u z)))) :
    (fun h => liftedTrace h hε (W h)) =o[atTop] (fun h : ℕ => ((2*h+2 : ℕ) : ℝ)) := by
  apply (Asymptotics.isLittleO_iff_tendsto (fun h hh => by
    have : (0 : ℝ) < ((2*h+2 : ℕ) : ℝ) := by positivity
    exact False.elim (this.ne' hh))).mpr
  have hi := nonreturning_integral_tendsto_zero u id hu measurable_id c hcmeas hY hC hc hregion hne
  have hre := (Complex.continuous_re.tendsto (0 : ℂ)).comp hi
  simp only [Complex.zero_re] at hre
  have hr : Tendsto (fun h : ℕ => ((2*h+1 : ℕ) : ℝ)/((2*h+2 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [norm_div, Complex.norm_natCast, norm_one] using weight_ratio_tendsto.norm
  have ht := (hr.div_const (4*Real.pi)).mul hre
  simp only [mul_zero] at ht
  apply ht.congr
  intro h
  dsimp only [Function.comp_apply, id]
  have hreg : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),
      Y ≤ (u z).im ∧ Y ≤ z.im ∧ (u z).im ≤ H ∧ z.im ≤ H :=
    hregion.mono (fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1⟩)
  rw [branch_trace_periodized h hε hY hC (W h) S hS hstrip u hu (c h) (hcmeas h) (hc h) hreg (hact h)]
  ring

#print axioms branch_trace_periodized
#print axioms nonreturning_branch_trace_isLittleO

end AsymptoticUnweightedKernel
