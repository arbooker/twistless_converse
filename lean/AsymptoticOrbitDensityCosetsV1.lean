module

public import AsymptoticOrbitDensityIndexV1
public import AsymptoticOrbitDensityIndependenceV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticOrbitDensity

open MeasureTheory
open scoped ENNReal

variable {G α : Type*} [Group G] [MulAction G α]
  (H : Subgroup G) (ρ : α → ℝ≥0∞)

/-- Summing ambient quotient densities over left-coset representatives
 gives a quotient density for the subgroup. -/
def inducedDensity (x : α) : ℝ≥0∞ := ∑' q : G ⧸ H, ρ (q.out • x)

theorem inducedDensity_normalized (hn : ∀ x, ∑' g : G, ρ (g • x) = 1) (x : α) :
    ∑' h : H, inducedDensity H ρ (h.val • x) = 1 := by
  simp only [inducedDensity]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]
  have he : (∑' p : (G ⧸ H) × H, ρ (p.1.out • (p.2.val • x))) =
      ∑' g : G, ρ (g • x) := by
    calc
      _ = ∑' p : (G ⧸ H) × H, ρ (leftProductEquiv H p • x) := by
        apply tsum_congr
        intro p
        exact congrArg ρ (mul_smul p.1.out p.2.val x).symm
      _ = _ := (leftProductEquiv H).tsum_eq (fun g => ρ (g • x))
  exact he.trans (hn x)

variable [MeasurableSpace α] [Countable G] [Finite (G ⧸ H)]
  (μ : Measure α) (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
  (hρ : Measurable ρ)

include hmp hρ in
omit [Countable G] in
theorem inducedDensity_measurable : Measurable (inducedDensity H ρ) := by
  exact Measurable.tsum (fun q => hρ.comp (hmp q.out).measurable)

include hmp hρ in
omit [Countable G] in
/-- The induced quotient density has the expected finite-index mass. -/
theorem inducedDensity_mass :
    (∫⁻ x, inducedDensity H ρ x ∂μ) = (H.index : ℝ≥0∞) * ∫⁻ x, ρ x ∂μ := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  simp only [inducedDensity]
  rw [lintegral_tsum]
  · have he (q : G ⧸ H) : (∫⁻ x, ρ (q.out • x) ∂μ) = ∫⁻ x, ρ x ∂μ :=
      (hmp q.out).lintegral_comp hρ
    simp only [he, tsum_fintype, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Subgroup.index, Fintype.card_eq_nat_card]
  · intro q
    exact (hρ.comp (hmp q.out).measurable).aemeasurable

include hmp hρ in
omit [Countable G] in
theorem inducedDensity_finite
    (hi : (∫⁻ x, ρ x ∂μ) ≠ ∞) : IsFiniteMeasure (μ.withDensity (inducedDensity H ρ)) := by
  apply isFiniteMeasure_withDensity
  rw [inducedDensity_mass H ρ μ hmp hρ]
  exact ENNReal.mul_ne_top (by simp) hi

variable (σ : α → ℝ≥0∞) (hσ : Measurable σ)
  (hnρ : ∀ x, ∑' g : G, ρ (g • x) = 1)
  (hnσ : ∀ x, ∑' h : H, σ (h.val • x) = 1)

include hmp hρ hσ hnρ hnσ in
/-- The induced density can replace any normalized subgroup density in
 the integral of an invariant complex function. -/
theorem integral_inducedDensity (f : α → ℂ) (hf : Measurable f)
    (hinv : ∀ h : H, ∀ x, f (h.val • x) = f x)
    (hi : Integrable f (μ.withDensity (inducedDensity H ρ)))
    (hiσ : Integrable f (μ.withDensity σ)) :
    (∫ x, f x ∂μ.withDensity (inducedDensity H ρ)) =
      ∫ x, f x ∂μ.withDensity σ := by
  exact integral_complex_invariant_eq (G := H) μ (fun h => hmp h.val)
    (inducedDensity H ρ) σ (inducedDensity_measurable H ρ μ hmp hρ) hσ
    (inducedDensity_normalized H ρ hnρ) hnσ f hf hinv hi hiσ

#print axioms inducedDensity_normalized
#print axioms inducedDensity_measurable
#print axioms inducedDensity_mass
#print axioms inducedDensity_finite
#print axioms integral_inducedDensity

end AsymptoticOrbitDensity
