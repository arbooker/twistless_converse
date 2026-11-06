module

public import AsymptoticFourierKernelTermBoundV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open UpperHalfPlane MeasureTheory

theorem hyperbolicKernelTerm_measurable {α : Type*} [MeasurableSpace α]
    (h n : ℕ) {ε : ℝ} (hε : 0 < ε) (z u : α → ℍ)
    (hz : Measurable z) (hu : Measurable u) :
    Measurable (fun x => hyperbolicKernelTerm h n ε (z x) (u x)) := by
  simp only [hyperbolicKernelTerm, kernelTerm_formula h n hε]
  unfold difference
  simp only [UpperHalfPlane.im]
  have hz' : Measurable (fun x => (z x : ℂ)) := UpperHalfPlane.measurable_coe.comp hz
  have hu' : Measurable (fun x => (u x : ℂ)) := UpperHalfPlane.measurable_coe.comp hu
  fun_prop

/-- Interchange the actual normalized Fourier-mode sum with a compactly
supported branch integral. The hypotheses require only measurable cell
rules and bounded coefficients; the summable majorant is proved here. -/
theorem hasSum_integral_kernel {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (h : ℕ) {ε Y H C : ℝ}
    (hε : 0 < ε) (hY : 0 < Y) (hC : 0 ≤ C)
    (z u : α → ℍ) (hz : Measurable z) (hu : Measurable u) (c : α → ℂ)
    (hcmeas : AEStronglyMeasurable c μ) (hc : ∀ᵐ x ∂μ, ‖c x‖ ≤ C)
    (hregion : ∀ᵐ x ∂μ, Y ≤ (z x).im ∧ Y ≤ (u x).im ∧ (z x).im ≤ H ∧ (u x).im ≤ H) :
    HasSum (fun n : ℕ => ∫ x, c x * hyperbolicKernelTerm h n ε (z x) (u x) ∂μ)
      (∫ x, c x * ((z x).im*(u x).im : ℝ) * fourierKernel h ε (z x) (u x) ∂μ) := by
  have hs := (termMajorant_summable h hY H).mul_left C
  apply hasSum_integral_of_dominated_convergence (fun n _x => C * termMajorant h Y H n)
  · intro n
    exact hcmeas.mul ((hyperbolicKernelTerm_measurable h n hε z u hz hu).aestronglyMeasurable)
  · intro n
    filter_upwards [hc, hregion] with x hcx hx
    rw [norm_mul]
    exact mul_le_mul hcx (hyperbolicKernelTerm_bound h n hε hY (z x) (u x)
      hx.1 hx.2.1 hx.2.2.1 hx.2.2.2) (norm_nonneg _) hC
  · exact Filter.Eventually.of_forall (fun _ => hs)
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro x
    have hh := (kernelTerm_summable h hε (z x) (u x)).hasSum.mul_left
      (c x * ((z x).im*(u x).im : ℝ))
    simpa only [hyperbolicKernelTerm, fourierKernel, mul_assoc] using hh

theorem integral_kernel_eq_tsum {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (h : ℕ) {ε Y H C : ℝ}
    (hε : 0 < ε) (hY : 0 < Y) (hC : 0 ≤ C)
    (z u : α → ℍ) (hz : Measurable z) (hu : Measurable u) (c : α → ℂ)
    (hcmeas : AEStronglyMeasurable c μ) (hc : ∀ᵐ x ∂μ, ‖c x‖ ≤ C)
    (hregion : ∀ᵐ x ∂μ, Y ≤ (z x).im ∧ Y ≤ (u x).im ∧ (z x).im ≤ H ∧ (u x).im ≤ H) :
    (∫ x, c x * ((z x).im*(u x).im : ℝ) * fourierKernel h ε (z x) (u x) ∂μ) =
      ∑' n : ℕ, ∫ x, c x * hyperbolicKernelTerm h n ε (z x) (u x) ∂μ :=
  (hasSum_integral_kernel h hε hY hC z u hz hu c hcmeas hc hregion).tsum_eq.symm

#print axioms hyperbolicKernelTerm_measurable
#print axioms hasSum_integral_kernel
#print axioms integral_kernel_eq_tsum

end AsymptoticUnweightedKernel
