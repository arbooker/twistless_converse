module

public import AsymptoticMassTransportV1
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticOrbitDensity

open MeasureTheory
open scoped ENNReal

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
  (μ : Measure α) (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
  (ρ σ : α → ℝ≥0∞) (hρ : Measurable ρ) (hσ : Measurable σ)
  (hnρ : ∀ x, ∑' g : G, ρ (g • x) = 1) (hnσ : ∀ x, ∑' g : G, σ (g • x) = 1)

include hmp hρ hσ hnρ hnσ

/-- Normalized orbit densities give the same integral of every invariant
 nonnegative function, by the proved countable mass-transport identity. -/
theorem lintegral_invariant_mul_eq (f : α → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ g : G, ∀ x, f (g • x) = f x) :
    (∫⁻ x, f x * ρ x ∂μ) = ∫⁻ x, f x * σ x ∂μ := by
  have ht := AsymptoticMassTransport.indexed_transport hmp
    (fun g x => f x * ρ x * σ (g • x))
    (fun g => (hf.mul hρ).mul (hσ.comp (hmp g).measurable))
  simp only [hinv, inv_smul_smul, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
    hnσ, hnρ, mul_one] at ht
  exact ht

theorem lintegral_invariant_eq (f : α → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ g : G, ∀ x, f (g • x) = f x) :
    (∫⁻ x, f x ∂μ.withDensity ρ) = ∫⁻ x, f x ∂μ.withDensity σ := by
  rw [lintegral_withDensity_eq_lintegral_mul μ hρ hf,
    lintegral_withDensity_eq_lintegral_mul μ hσ hf]
  simpa only [Pi.mul_apply, mul_comm] using
    lintegral_invariant_mul_eq μ hmp ρ σ hρ hσ hnρ hnσ f hf hinv

/-- Density independence extends to real integrable invariant functions. -/
theorem integral_real_invariant_eq (f : α → ℝ) (hf : Measurable f)
    (hinv : ∀ g : G, ∀ x, f (g • x) = f x)
    (hiρ : Integrable f (μ.withDensity ρ)) (hiσ : Integrable f (μ.withDensity σ)) :
    (∫ x, f x ∂μ.withDensity ρ) = ∫ x, f x ∂μ.withDensity σ := by
  have hp := lintegral_invariant_eq μ hmp ρ σ hρ hσ hnρ hnσ
    (fun x => ENNReal.ofReal (f x)) hf.ennreal_ofReal (by intro g x; rw [hinv])
  have hn := lintegral_invariant_eq μ hmp ρ σ hρ hσ hnρ hnσ
    (fun x => ENNReal.ofReal (-f x)) hf.neg.ennreal_ofReal (by intro g x; rw [hinv])
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hiρ,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hiσ, hp, hn]

/-- In particular the complex Petersson integral is independent of the
 normalized orbit density used to represent the quotient. -/
theorem integral_complex_invariant_eq (f : α → ℂ) (hf : Measurable f)
    (hinv : ∀ g : G, ∀ x, f (g • x) = f x)
    (hiρ : Integrable f (μ.withDensity ρ)) (hiσ : Integrable f (μ.withDensity σ)) :
    (∫ x, f x ∂μ.withDensity ρ) = ∫ x, f x ∂μ.withDensity σ := by
  apply Complex.ext
  · change RCLike.re (∫ x, f x ∂μ.withDensity ρ) = RCLike.re (∫ x, f x ∂μ.withDensity σ)
    rw [← integral_re hiρ, ← integral_re hiσ]
    exact integral_real_invariant_eq μ hmp ρ σ hρ hσ hnρ hnσ
      (fun x => (f x).re) (Complex.measurable_re.comp hf)
      (fun g x => congrArg Complex.re (hinv g x)) hiρ.re hiσ.re
  · change RCLike.im (∫ x, f x ∂μ.withDensity ρ) = RCLike.im (∫ x, f x ∂μ.withDensity σ)
    rw [← integral_im hiρ, ← integral_im hiσ]
    exact integral_real_invariant_eq μ hmp ρ σ hρ hσ hnρ hnσ
      (fun x => (f x).im) (Complex.measurable_im.comp hf)
      (fun g x => congrArg Complex.im (hinv g x)) hiρ.im hiσ.im

#print axioms lintegral_invariant_mul_eq
#print axioms lintegral_invariant_eq
#print axioms integral_real_invariant_eq
#print axioms integral_complex_invariant_eq

end AsymptoticOrbitDensity
