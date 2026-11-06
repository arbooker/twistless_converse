module

public import AsymptoticOrbitDensityTransportV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticOrbitDensity

open MeasureTheory
open scoped ENNReal

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
  (μ : Measure α) (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
  (H : Subgroup G) [Fintype (G ⧸ H)] (ρ : α → ℝ≥0∞) (hρ : Measurable ρ)
  (hnρ : ∀ x, ∑' h : H, ρ (h.val • x) = 1)
  (hfin : (∫⁻ x, ρ x ∂μ) ≠ ∞)

include hmp hρ hnρ hfin

/-- Coset averaging of a bounded subgroup-invariant function preserves
 its subgroup quotient integral after division by the index. -/
theorem integral_coset_average (f : α → ℂ) (hf : Measurable f)
    (hinv : ∀ h : H, ∀ x, f (h.val • x) = f x)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    ((H.index : ℝ)⁻¹) •
      (∫ x, ∑ q : G ⧸ H, f (q.out⁻¹ • x) ∂μ.withDensity ρ) =
        ∫ x, f x ∂μ.withDensity ρ := by
  let σ : α → ℝ≥0∞ := fun x => (H.index : ℝ≥0∞)⁻¹ * ρ x
  have hσ : Measurable σ := measurable_const.mul hρ
  have hnσ (x : α) : ∑' g : G, σ (g • x) = 1 := by
    simp only [σ, ENNReal.tsum_mul_left]
    rw [subgroup_mass_eq_index H ρ hnρ]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast H.index_ne_zero_of_finite) (by simp)
  have hfinσ : (∫⁻ x, σ x ∂μ) ≠ ∞ := by
    rw [show (∫⁻ x, σ x ∂μ) = (H.index : ℝ≥0∞)⁻¹ * ∫⁻ x, ρ x ∂μ from
      lintegral_const_mul _ hρ]
    exact ENNReal.mul_ne_top (by simpa using H.index_ne_zero_of_finite) hfin
  let : IsFiniteMeasure (μ.withDensity ρ) := isFiniteMeasure_withDensity hfin
  let : IsFiniteMeasure (μ.withDensity (inducedDensity H σ)) :=
    inducedDensity_finite H σ μ hmp hσ hfinσ
  have hiρ : Integrable f (μ.withDensity ρ) := memLp_one_iff_integrable.mp
    (MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC))
  have hi : Integrable f (μ.withDensity (inducedDensity H σ)) := memLp_one_iff_integrable.mp
    (MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC))
  have he := integral_inducedDensity H σ μ hmp hσ ρ hρ hnσ hnρ f hf hinv hi hiρ
  rw [← integral_coset_unfold μ hmp σ hσ H hfinσ f hf C hC] at he
  have hm : μ.withDensity σ = (H.index : ℝ≥0∞)⁻¹ • μ.withDensity ρ :=
    withDensity_smul _ hρ
  rw [hm, integral_smul_measure] at he
  simpa only [ENNReal.toReal_inv, ENNReal.toReal_natCast] using he

#print axioms integral_coset_average

end AsymptoticOrbitDensity
