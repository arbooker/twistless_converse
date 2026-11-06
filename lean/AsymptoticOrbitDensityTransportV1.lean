module

public import AsymptoticOrbitDensityCosetsV1
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticOrbitDensity

open MeasureTheory
open scoped ENNReal

variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
  (μ : Measure α) (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
  (ρ : α → ℝ≥0∞) (hρ : Measurable ρ)

include hmp hρ

/-- Translation transfers an inverse action on the integrand to a
 forward action on the quotient density. -/
theorem lintegral_translate_density (g : G) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (g⁻¹ • x) ∂μ.withDensity ρ) =
      ∫⁻ x, f x ∂μ.withDensity (fun x => ρ (g • x)) := by
  have hf' : Measurable (fun x => f (g⁻¹ • x)) := hf.comp (hmp g⁻¹).measurable
  have hρ' : Measurable (fun x => ρ (g • x)) := hρ.comp (hmp g).measurable
  rw [lintegral_withDensity_eq_lintegral_mul μ hρ hf',
    lintegral_withDensity_eq_lintegral_mul μ hρ' hf]
  have he := (hmp g).lintegral_comp (hρ.mul (hf.comp (hmp g⁻¹).measurable))
  simpa only [Pi.mul_apply, Function.comp_apply, inv_smul_smul] using he.symm

theorem integral_real_translate_density (g : G) (f : α → ℝ) (hf : Measurable f)
    (hi : Integrable (fun x => f (g⁻¹ • x)) (μ.withDensity ρ))
    (hi' : Integrable f (μ.withDensity (fun x => ρ (g • x)))) :
    (∫ x, f (g⁻¹ • x) ∂μ.withDensity ρ) =
      ∫ x, f x ∂μ.withDensity (fun x => ρ (g • x)) := by
  have hp := lintegral_translate_density μ hmp ρ hρ g
    (fun x => ENNReal.ofReal (f x)) hf.ennreal_ofReal
  have hn := lintegral_translate_density μ hmp ρ hρ g
    (fun x => ENNReal.ofReal (-f x)) hf.neg.ennreal_ofReal
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi', hp, hn]

theorem integral_complex_translate_density (g : G) (f : α → ℂ) (hf : Measurable f)
    (hi : Integrable (fun x => f (g⁻¹ • x)) (μ.withDensity ρ))
    (hi' : Integrable f (μ.withDensity (fun x => ρ (g • x)))) :
    (∫ x, f (g⁻¹ • x) ∂μ.withDensity ρ) =
      ∫ x, f x ∂μ.withDensity (fun x => ρ (g • x)) := by
  apply Complex.ext
  · change RCLike.re (∫ x, f (g⁻¹ • x) ∂μ.withDensity ρ) =
      RCLike.re (∫ x, f x ∂μ.withDensity (fun x => ρ (g • x)))
    rw [← integral_re hi, ← integral_re hi']
    exact integral_real_translate_density μ hmp ρ hρ g
      (fun x => (f x).re) (Complex.measurable_re.comp hf) hi.re hi'.re
  · change RCLike.im (∫ x, f (g⁻¹ • x) ∂μ.withDensity ρ) =
      RCLike.im (∫ x, f x ∂μ.withDensity (fun x => ρ (g • x)))
    rw [← integral_im hi, ← integral_im hi']
    exact integral_real_translate_density μ hmp ρ hρ g
      (fun x => (f x).im) (Complex.measurable_im.comp hf) hi.im hi'.im

/-- Finite-coset unfolding for bounded complex functions against a
 finite quotient measure. Integrability on both sides is derived. -/
theorem integral_coset_unfold (H : Subgroup G) [Fintype (G ⧸ H)]
    (hfin : (∫⁻ x, ρ x ∂μ) ≠ ∞)
    (f : α → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, ∑ q : G ⧸ H, f (q.out⁻¹ • x) ∂μ.withDensity ρ) =
      ∫ x, f x ∂μ.withDensity (inducedDensity H ρ) := by
  classical
  let : IsFiniteMeasure (μ.withDensity ρ) := isFiniteMeasure_withDensity hfin
  have hi (q : G ⧸ H) : Integrable (fun x => f (q.out⁻¹ • x)) (μ.withDensity ρ) := by
    apply memLp_one_iff_integrable.mp
    exact MemLp.of_bound (hf.comp (hmp q.out⁻¹).measurable).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun x => hC _))
  have hi' (q : G ⧸ H) : Integrable f (μ.withDensity (fun x => ρ (q.out • x))) := by
    let : IsFiniteMeasure (μ.withDensity (fun x => ρ (q.out • x))) := by
      apply isFiniteMeasure_withDensity
      rw [(hmp q.out).lintegral_comp hρ]
      exact hfin
    exact memLp_one_iff_integrable.mp
      (MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC))
  have hd : μ.withDensity (inducedDensity H ρ) =
      ∑ q : G ⧸ H, μ.withDensity (fun x => ρ (q.out • x)) := by
    have he : inducedDensity H ρ = ∑' q : G ⧸ H, (fun x => ρ (q.out • x)) := by
      funext x
      simp only [inducedDensity, tsum_fintype, Finset.sum_apply]
    rw [he, withDensity_tsum (f := fun q : G ⧸ H => fun x => ρ (q.out • x))
      (fun q => hρ.comp (hmp q.out).measurable), Measure.sum_fintype]
  rw [integral_finsetSum Finset.univ (fun q _ => hi q), hd,
    integral_finsetSum_measure (fun q _ => hi' q)]
  apply Finset.sum_congr rfl
  intro q _
  exact integral_complex_translate_density μ hmp ρ hρ q.out f hf (hi q) (hi' q)

#print axioms lintegral_translate_density
#print axioms integral_real_translate_density
#print axioms integral_complex_translate_density
#print axioms integral_coset_unfold

end AsymptoticOrbitDensity
