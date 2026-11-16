module

public import QuantitativeMaassOrbitIntegralV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QuantitativeMaass

/-- Actual nonnegative Poincaré unfolding against a normalized orbit
weight. Tonelli proves the interchange, with no finiteness assumption. -/
theorem lintegral_poincare_unfold {G A : Type*} [Group G] [Countable G]
    [MulAction G A] [MeasurableSpace A] (μ : Measure A)
    (hmp : ∀ g : G, MeasurePreserving (fun x : A => g • x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ)
    (hn : ∀ x, ∑' g : G, ρ (g • x)=1)
    (F : A → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, ∑' g : G, F (g • x) ∂μ.withDensity ρ)=∫⁻ x, F x ∂μ := by
  have hm (g : G) : Measurable (fun x => F (g•x)) := hF.comp (hmp g).measurable
  rw [lintegral_withDensity_eq_lintegral_mul μ hρ (Measurable.tsum hm)]
  simp only [Pi.mul_apply,← ENNReal.tsum_mul_left]
  rw [lintegral_tsum (f := fun g x => ρ x*F (g•x))
    (fun g => (hρ.mul (hm g)).aemeasurable)]
  have he (g : G) : (∫⁻ x, ρ x*F (g•x) ∂μ)=∫⁻ x, ρ (g⁻¹•x)*F x ∂μ := by
    have ht := (hmp g⁻¹).lintegral_comp (hρ.mul (hm g))
    simpa only [Pi.mul_apply,Function.comp_apply,smul_inv_smul] using ht.symm
  simp_rw [he]
  rw [← lintegral_tsum (f := fun g x => ρ (g⁻¹•x)*F x) (fun g => ((hρ.comp (hmp g⁻¹).measurable).mul hF).aemeasurable)]
  apply lintegral_congr
  intro x
  rw [ENNReal.tsum_mul_right]
  have hi : (∑' g : G, ρ (g⁻¹•x))=1 :=
    ((Equiv.inv G).tsum_eq (fun g => ρ (g•x))).trans (hn x)
  rw [hi,one_mul]

#print axioms lintegral_poincare_unfold

end QuantitativeMaass
