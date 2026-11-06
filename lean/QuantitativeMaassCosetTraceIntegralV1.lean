module

public import QuantitativeMaassCosetTraceNormV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace QuantitativeMaass.CosetTrace

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
    (μ : Measure α) (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (H : Subgroup G) [Fintype (G ⧸ H)]
    (ρ σ : α → ℝ≥0∞) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hnρ : ∀ x, ∑' g : G, ρ (g • x) = 1)
    (hnσ : ∀ x, ∑' h : H, σ (h.val • x) = 1)

include hmp hρ hσ hnρ hnσ in
/-- Finite-coset unfolding for every integrable automorphic function; no
pointwise boundedness assumption is used. -/
theorem integral_unfold (f : α → ℂ) (hf : Measurable f)
    (hinv : ∀ h : H, ∀ x, f (h.val • x) = f x)
    (hiσ : Integrable f (μ.withDensity σ)) :
    (∫ x, trace H f hinv x ∂μ.withDensity ρ) = ∫ x, f x ∂μ.withDensity σ := by
  let τ := AsymptoticOrbitDensity.inducedDensity H ρ
  have hτ : Measurable τ := AsymptoticOrbitDensity.inducedDensity_measurable H ρ μ hmp hρ
  have hnτ := AsymptoticOrbitDensity.inducedDensity_normalized H ρ hnρ
  have henorm : eLpNorm f 1 (μ.withDensity τ) = eLpNorm f 1 (μ.withDensity σ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (μ := μ.withDensity τ) hf.aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm (μ := μ.withDensity σ) hf.aestronglyMeasurable]
    exact AsymptoticOrbitDensity.lintegral_invariant_eq μ (fun h : H => hmp h.val)
      τ σ hτ hσ hnτ hnσ (fun x => ‖f x‖ₑ) (by fun_prop) (by intro h x; exact congrArg (fun z : ℂ => ‖z‖ₑ) (hinv h x))
  have hiτ : Integrable f (μ.withDensity τ) := by
    apply memLp_one_iff_integrable.mp
    change eLpNorm f 1 (μ.withDensity τ) < ∞
    rw [henorm]
    exact memLp_one_iff_integrable.mpr hiσ
  have hi' (q : G ⧸ H) : Integrable f (μ.withDensity (fun x => ρ (q.out • x))) := by
    apply hiτ.mono_measure
    apply withDensity_mono
    exact Filter.Eventually.of_forall (fun x => ENNReal.le_tsum (f := fun q : G ⧸ H => ρ (q.out • x)) q)
  have hi (q : G ⧸ H) : Integrable (fun x => f (q.out⁻¹ • x)) (μ.withDensity ρ) := by
    apply memLp_one_iff_integrable.mp
    change eLpNorm (fun x => f (q.out⁻¹ • x)) 1 (μ.withDensity ρ) < ∞
    rw [eLpNorm_one_eq_lintegral_enorm (μ := μ.withDensity ρ)
      (f := fun x => f (q.out⁻¹ • x)) (hf.comp (hmp q.out⁻¹).measurable).aestronglyMeasurable]
    have he := AsymptoticOrbitDensity.lintegral_translate_density μ hmp ρ hρ q.out
      (fun x => ‖f x‖ₑ) (by fun_prop)
    rw [he]
    rw [← eLpNorm_one_eq_lintegral_enorm (μ := μ.withDensity (fun x => ρ (q.out • x)))
      hf.aestronglyMeasurable]
    exact memLp_one_iff_integrable.mpr (hi' q)
  have hd : μ.withDensity τ = ∑ q : G ⧸ H, μ.withDensity (fun x => ρ (q.out • x)) := by
    have he : τ = ∑' q : G ⧸ H, (fun x => ρ (q.out • x)) := by
      funext x
      simp only [τ, AsymptoticOrbitDensity.inducedDensity, tsum_fintype, Finset.sum_apply]
    rw [he, withDensity_tsum (f := fun q : G ⧸ H => fun x => ρ (q.out • x))
      (fun q => hρ.comp (hmp q.out).measurable), Measure.sum_fintype]
  calc
    _ = ∑ q : G ⧸ H, ∫ x, f (q.out⁻¹ • x) ∂μ.withDensity ρ := by
      simp only [trace_out]
      exact integral_finsetSum Finset.univ (fun q _ => hi q)
    _ = ∑ q : G ⧸ H, ∫ x, f x ∂μ.withDensity (fun x => ρ (q.out • x)) := by
      apply Finset.sum_congr rfl
      intro q _
      exact AsymptoticOrbitDensity.integral_complex_translate_density μ hmp ρ hρ q.out f hf
        (hi q) (hi' q)
    _ = ∫ x, f x ∂μ.withDensity τ := by
      rw [hd, integral_finsetSum_measure (fun q _ => hi' q)]
    _ = _ := AsymptoticOrbitDensity.integral_complex_invariant_eq μ (fun h : H => hmp h.val)
      τ σ hτ hσ hnτ hnσ f hf hinv hiτ hiσ

#print axioms integral_unfold

end QuantitativeMaass.CosetTrace
