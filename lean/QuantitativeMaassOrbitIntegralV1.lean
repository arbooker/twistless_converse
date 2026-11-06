module

public import AsymptoticOrbitDensityNormalizerV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QuantitativeMaass.OrbitIntegral

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
    (μ : Measure α) (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)

include hmp

/-- A quotient normalizer preserves every nonnegative measurable invariant
integral; no boundedness or integrability assumption is required. -/
theorem lintegral_normalizer (H : Subgroup G) (g : G)
    (hc : ∀ a ∈ H, g * a * g⁻¹ ∈ H) (hci : ∀ a ∈ H, g⁻¹ * a * g ∈ H)
    (ρ : α → ℝ≥0∞) (hρ : Measurable ρ)
    (hn : ∀ x, ∑' a : H, ρ (a.val • x) = 1)
    (f : α → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ a : H, ∀ x, f (a.val • x) = f x) :
    (∫⁻ x, f (g • x) ∂μ.withDensity ρ) = ∫⁻ x, f x ∂μ.withDensity ρ := by
  let σ : α → ℝ≥0∞ := fun x => ρ (g⁻¹ • x)
  have hσ : Measurable σ := hρ.comp (hmp g⁻¹).measurable
  have hnσ (x : α) : ∑' a : H, σ (a.val • x) = 1 :=
    AsymptoticOrbitDensity.translated_density_normalized H g⁻¹
      (by simpa only [inv_inv] using hci) (by simpa only [inv_inv] using hc) ρ hn x
  calc
    _ = ∫⁻ x, f x ∂μ.withDensity σ := by
      simpa only [inv_inv] using
        AsymptoticOrbitDensity.lintegral_translate_density μ hmp ρ hρ g⁻¹ f hf
    _ = _ := AsymptoticOrbitDensity.lintegral_invariant_eq μ (fun a : H => hmp a.val)
      σ ρ hσ hρ hnσ hn f hf hinv

/-- Finite-cover unfolding for a nonnegative function invariant under the
ambient group. Its norm mass is multiplied by the actual subgroup index. -/
theorem lintegral_finite_cover (H : Subgroup G) [Finite (G ⧸ H)]
    (ρ σ : α → ℝ≥0∞) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hnρ : ∀ x, ∑' g : G, ρ (g • x) = 1)
    (hnσ : ∀ x, ∑' h : H, σ (h.val • x) = 1)
    (f : α → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ g : G, ∀ x, f (g • x) = f x) :
    (∫⁻ x, f x ∂μ.withDensity σ) =
      (H.index : ℝ≥0∞) * ∫⁻ x, f x ∂μ.withDensity ρ := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  have hi := AsymptoticOrbitDensity.lintegral_invariant_eq μ (fun h : H => hmp h.val)
    σ (AsymptoticOrbitDensity.inducedDensity H ρ) hσ
    (AsymptoticOrbitDensity.inducedDensity_measurable H ρ μ hmp hρ) hnσ
    (AsymptoticOrbitDensity.inducedDensity_normalized H ρ hnρ) f hf
    (fun h x => hinv h.val x)
  rw [hi, lintegral_withDensity_eq_lintegral_mul μ
    (AsymptoticOrbitDensity.inducedDensity_measurable H ρ μ hmp hρ) hf]
  simp only [Pi.mul_apply, AsymptoticOrbitDensity.inducedDensity, ← ENNReal.tsum_mul_right]
  rw [lintegral_tsum (μ := μ) (f := fun q : G ⧸ H => fun x => ρ (q.out • x) * f x) (fun q : G ⧸ H => ((hρ.comp (hmp q.out).measurable).mul hf).aemeasurable)]
  have he (q : G ⧸ H) : (∫⁻ x, ρ (q.out • x) * f x ∂μ) =
      ∫⁻ x, f x ∂μ.withDensity ρ := by
    rw [lintegral_withDensity_eq_lintegral_mul μ hρ hf]
    simpa only [Pi.mul_apply, hinv] using (hmp q.out).lintegral_comp (hρ.mul hf)
  simp only [he, tsum_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Subgroup.index, Fintype.card_eq_nat_card]

#print axioms lintegral_normalizer
#print axioms lintegral_finite_cover

end QuantitativeMaass.OrbitIntegral
