module

public import AsymptoticOrbitDensityTransportV1
public import AsymptoticOrbitDensityIndependenceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticOrbitDensity

open MeasureTheory
open scoped ENNReal

variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
variable (H : Subgroup G) (g : G)
variable (hc : ∀ a ∈ H, g * a * g⁻¹ ∈ H) (hci : ∀ a ∈ H, g⁻¹ * a * g ∈ H)

/-- Conjugation by a normalizer permutes the subgroup itself. -/
def normalizerEquiv : H ≃ H where
  toFun a := ⟨g * a.val * g⁻¹, hc a.val a.property⟩
  invFun a := ⟨g⁻¹ * a.val * g, hci a.val a.property⟩
  left_inv a := by apply Subtype.ext; change g⁻¹ * (g * a.val * g⁻¹) * g = a.val; group
  right_inv a := by apply Subtype.ext; change g * (g⁻¹ * a.val * g) * g⁻¹ = a.val; group

include hc hci in
omit [MeasurableSpace α] in
/-- Translation by a normalizer preserves the orbit-density normalization. -/
theorem translated_density_normalized (ρ : α → ℝ≥0∞)
    (hn : ∀ x, ∑' a : H, ρ (a.val • x) = 1) (x : α) :
    (∑' a : H, ρ (g • (a.val • x))) = 1 := by
  have he := (normalizerEquiv H g hc hci).tsum_eq (fun a : H => ρ (a.val • (g • x)))
  have hh (a : H) : (normalizerEquiv H g hc hci a).val • (g • x) = g • (a.val • x) := by
    change (g * a.val * g⁻¹) • (g • x) = _
    simp only [mul_smul, inv_smul_smul]
  simp_rw [hh] at he
  exact he.trans (hn (g • x))

variable [Countable G]
variable (μ : Measure α) (hmp : ∀ a : G, MeasurePreserving (fun x : α => a • x) μ μ)
variable (ρ : α → ℝ≥0∞) (hρ : Measurable ρ)
variable (hn : ∀ x, ∑' a : H, ρ (a.val • x) = 1)
variable (hfin : (∫⁻ x, ρ x ∂μ) ≠ ∞)

include hc hci hmp hρ hn hfin in
/-- A rational normalizer preserves the quotient integral of every bounded
 invariant complex function. Both sides are genuinely integrable. -/
theorem integral_normalizer (f : α → ℂ) (hf : Measurable f)
    (hinv : ∀ a : H, ∀ x, f (a.val • x) = f x)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f (g • x) ∂μ.withDensity ρ) = ∫ x, f x ∂μ.withDensity ρ := by
  let σ : α → ℝ≥0∞ := fun x => ρ (g⁻¹ • x)
  have hσ : Measurable σ := hρ.comp (hmp g⁻¹).measurable
  have hnσ (x : α) : ∑' a : H, σ (a.val • x) = 1 := by
    exact translated_density_normalized H g⁻¹ (by simpa only [inv_inv] using hci)
      (by simpa only [inv_inv] using hc) ρ hn x
  have hfinσ : (∫⁻ x, σ x ∂μ) ≠ ∞ := by
    have he := (hmp g⁻¹).lintegral_comp hρ
    change (∫⁻ x, ρ (g⁻¹ • x) ∂μ) ≠ ∞
    rw [he]
    exact hfin
  let : IsFiniteMeasure (μ.withDensity ρ) := isFiniteMeasure_withDensity hfin
  let : IsFiniteMeasure (μ.withDensity σ) := isFiniteMeasure_withDensity hfinσ
  have hi : Integrable f (μ.withDensity ρ) :=
    memLp_one_iff_integrable.mp (MemLp.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC))
  have hiσ : Integrable f (μ.withDensity σ) :=
    memLp_one_iff_integrable.mp (MemLp.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC))
  have hig : Integrable (fun x => f (g • x)) (μ.withDensity ρ) :=
    memLp_one_iff_integrable.mp (MemLp.of_bound
      (hf.comp (hmp g).measurable).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun x => hC (g • x))))
  calc
    _ = ∫ x, f x ∂μ.withDensity σ := by
      simpa only [inv_inv] using integral_complex_translate_density μ hmp ρ hρ g⁻¹ f hf
        (by simpa only [inv_inv] using hig) hiσ
    _ = _ := (integral_complex_invariant_eq (G := H) μ (fun a => hmp a.val)
      ρ σ hρ hσ hn hnσ f hf hinv hi hiσ).symm

#print axioms normalizerEquiv
#print axioms translated_density_normalized
#print axioms integral_normalizer

end AsymptoticOrbitDensity
