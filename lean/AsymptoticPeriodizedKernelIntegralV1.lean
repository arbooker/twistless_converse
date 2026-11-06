module

public import AsymptoticPeriodizedKernelBoundV1
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open UpperHalfPlane Filter MeasureTheory AsymptoticBergmanDecay
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem base_continuous : Continuous (fun p : ℍ × ℍ => base p.1 p.2) := by
  unfold base
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro p
  exact denominator_ne_zero p.1 p.2

theorem translate_continuous (n : ℤ) : Continuous (fun z : ℍ => translate z n) := by
  unfold translate
  fun_prop

theorem periodized_kernel_measurable {α : Type*} [MeasurableSpace α]
    (h : ℕ) (z u : α → ℍ) (hz : Measurable z) (hu : Measurable u) :
    Measurable (fun x => ∑' n : ℤ, base (translate (z x) n) (u x)^(2*h+2)) := by
  apply Measurable.tsum
  intro n
  unfold base translate
  simp only [UpperHalfPlane.im, Complex.add_im, Complex.intCast_im, add_zero]
  have hz' : Measurable (fun x => (z x : ℂ)) := UpperHalfPlane.measurable_coe.comp hz
  have hu' : Measurable (fun x => (u x : ℂ)) := UpperHalfPlane.measurable_coe.comp hu
  fun_prop

theorem compactKernelBound_nonneg (Y H R : ℝ) : 0 ≤ compactKernelBound Y H R := by
  apply mul_nonneg (sq_nonneg _)
  apply tsum_nonneg
  intro n
  unfold integerDecay
  positivity

/-- The nonreturning branch contribution tends to zero after division by
the Bergman prefactor, even when its bounded slash phase depends on the
weight. The periodization is the full infinite sum. -/
theorem nonreturning_integral_tendsto_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (z u : α → ℍ)
    (hz : Measurable z) (hu : Measurable u) (c : ℕ → α → ℂ)
    (hcmeas : ∀ h, AEStronglyMeasurable (c h) μ)
    {Y H R C : ℝ} (hY : 0 < Y) (hC : 0 ≤ C)
    (hc : ∀ h, ∀ᵐ x ∂μ, ‖c h x‖ ≤ C)
    (hregion : ∀ᵐ x ∂μ, Y ≤ (z x).im ∧ Y ≤ (u x).im ∧ (z x).im ≤ H ∧
      (u x).im ≤ H ∧ |(z x).re-(u x).re| ≤ R)
    (hne : ∀ᵐ x ∂μ, ∀ n : ℤ, translate (z x) n ≠ u x) :
    Tendsto (fun h : ℕ => ∫ x, c h x *
      (∑' n : ℤ, base (translate (z x) n) (u x)^(2*h+2)) ∂μ) atTop (𝓝 0) := by
  let D := compactKernelBound Y H R
  have hmeas (h : ℕ) : AEStronglyMeasurable (fun x => c h x *
      (∑' n : ℤ, base (translate (z x) n) (u x)^(2*h+2))) μ :=
    (hcmeas h).mul ((periodized_kernel_measurable h z u hz hu).aestronglyMeasurable)
  have hbound (h : ℕ) : ∀ᵐ x ∂μ, ‖c h x *
      (∑' n : ℤ, base (translate (z x) n) (u x)^(2*h+2))‖ ≤ C*D := by
    filter_upwards [hc h, hregion] with x hcx hx
    rw [norm_mul]
    exact mul_le_mul hcx
      (periodized_kernel_norm_bound h hY (z x) (u x) hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2)
      (norm_nonneg _) hC
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun h : ℕ => c h x *
      (∑' n : ℤ, base (translate (z x) n) (u x)^(2*h+2))) atTop (𝓝 (0 : ℂ)) := by
    filter_upwards [hne, ae_all_iff.mpr hc] with x hx hcx
    have hk := periodized_kernel_tendsto (z x) (u x)
    have hr : returnValue (z x) (u x) = 0 := by
      unfold returnValue
      exact ite_eq_right (fun ⟨n, hn⟩ => hx n hn)
    rw [hr] at hk
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (g:=fun h => C*‖∑' n : ℤ, base (translate (z x) n) (u x)^(2*h+2)‖)
      (fun _ => norm_nonneg _)
      (fun h => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hcx h) (norm_nonneg _))
    simpa only [norm_zero, mul_zero] using hk.norm.const_mul C
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun _ : α => C*D) hmeas (integrable_const _) hbound hlim

#print axioms periodized_kernel_measurable
#print axioms nonreturning_integral_tendsto_zero

end AsymptoticUnweightedKernel
