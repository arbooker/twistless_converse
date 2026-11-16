module

public import QuantitativeMaassPoincareUnfoldV1
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QuantitativeMaass

/-- Normalized orbit weights sum, after translation, to the ambient measure. -/
theorem orbit_translated_measure_sum {G A : Type*} [Group G] [Countable G]
    [MulAction G A] [MeasurableSpace A] (μ : Measure A)
    (hmp : ∀ g : G, MeasurePreserving (fun x : A => g • x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g • x)=1) :
    Measure.sum (fun g : G => μ.withDensity (fun x => ρ (g⁻¹•x)))=μ := by
  rw [← withDensity_tsum (f := fun g : G => fun x => ρ (g⁻¹•x))
    (fun g : G => hρ.comp (hmp g⁻¹).measurable)]
  have he : (∑' g : G, fun x => ρ (g⁻¹•x))=(1 : A → ℝ≥0∞) := by
    funext x
    rw [ENNReal.tsum_apply]
    exact ((Equiv.inv G).tsum_eq (fun g => ρ (g•x))).trans (hn x)
  rw [he,withDensity_one]

/-- Complex Poincaré unfolding for every integrable measurable seed.
Absolute integrability of the series and the Bochner/Tonelli interchange
are proved from the actual normalized orbit weight. -/
theorem integral_poincare_unfold {G A : Type*} [Group G] [Countable G]
    [MulAction G A] [MeasurableSpace A] (μ : Measure A)
    (hmp : ∀ g : G, MeasurePreserving (fun x : A => g • x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g • x)=1)
    (f : A → ℂ) (hf : Measurable f) (hi : Integrable f μ) :
    Integrable (fun x => ∑' g : G, f (g•x)) (μ.withDensity ρ) ∧
      (∫ x, ∑' g : G, f (g•x) ∂μ.withDensity ρ)=∫ x, f x ∂μ := by
  have hfm (g : G) : Measurable (fun x => f (g•x)) := hf.comp (hmp g).measurable
  have hnorm : (∫⁻ x, ∑' g : G, ‖f (g•x)‖ₑ ∂μ.withDensity ρ)=
      ∫⁻ x, ‖f x‖ₑ ∂μ := lintegral_poincare_unfold μ hmp ρ hρ hn _ hf.enorm
  have hsum : (∑' g : G, ∫⁻ x, ‖f (g•x)‖ₑ ∂μ.withDensity ρ)≠∞ := by
    rw [← lintegral_tsum (f := fun g x => ‖f (g•x)‖ₑ)
      (fun g => (hfm g).enorm.aemeasurable),hnorm]
    exact hi.2.ne
  have hseries : Integrable (fun x => ∑' g : G, f (g•x)) (μ.withDensity ρ) := by
    refine ⟨(Measurable.tsum hfm).aestronglyMeasurable,?_⟩
    change (∫⁻ x, ‖∑' g : G, f (g•x)‖ₑ ∂μ.withDensity ρ)<∞
    exact lt_of_le_of_lt (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm))
      (hnorm ▸ hi.2)
  refine ⟨hseries,?_⟩
  have hmeasure := orbit_translated_measure_sum μ hmp ρ hρ hn
  have hfi' (g : G) : Integrable f (μ.withDensity (fun x => ρ (g⁻¹•x))) := by
    exact hi.mono_measure ((Measure.le_sum
      (fun g : G => μ.withDensity (fun x => ρ (g⁻¹•x))) g).trans_eq hmeasure)
  have hfi (g : G) : Integrable (fun x => f (g•x)) (μ.withDensity ρ) := by
    refine ⟨(hfm g).aestronglyMeasurable,?_⟩
    change (∫⁻ x, ‖f (g•x)‖ₑ ∂μ.withDensity ρ)<∞
    exact lt_of_le_of_lt (ENNReal.le_tsum (f := fun g : G =>
      ∫⁻ x, ‖f (g•x)‖ₑ ∂μ.withDensity ρ) g) hsum.lt_top
  rw [integral_tsum (f := fun g x => f (g•x)) (fun g => (hfm g).aestronglyMeasurable) hsum]
  have he (g : G) : (∫ x, f (g•x) ∂μ.withDensity ρ)=
      ∫ x, f x ∂μ.withDensity (fun x => ρ (g⁻¹•x)) := by
    simpa only [inv_inv] using AsymptoticOrbitDensity.integral_complex_translate_density
      μ hmp ρ hρ g⁻¹ f hf (by simpa only [inv_inv] using hfi g) (hfi' g)
  simp_rw [he]
  have hisum : Integrable f (Measure.sum (fun g : G =>
      μ.withDensity (fun x => ρ (g⁻¹•x)))) := by rw [hmeasure]; exact hi
  exact (hasSum_integral_measure hisum).tsum_eq.trans (by rw [hmeasure])

#print axioms orbit_translated_measure_sum
#print axioms integral_poincare_unfold

end QuantitativeMaass
