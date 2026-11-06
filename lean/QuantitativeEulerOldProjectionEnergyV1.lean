module

public import QuantitativeEulerOldProjectionOrbitV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionPhysical

open MeasureTheory AsymptoticNestedQuotients
open scoped ENNReal lp

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
    (μ : Measure α) (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (H : Subgroup G) [H.FiniteIndex] (σ : α → ℝ≥0∞) (hσ : Measurable σ)
    (hnσ : ∀ x, ∑' h : H, σ (h.val • x) = 1)

local instance : Fintype (G ⧸ H) := Fintype.ofFinite _
local instance : Finite (Classes H) := Finite.of_equiv (G ⧸ H)
  (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
local instance : Fintype (Classes H) := Fintype.ofFinite _

variable (f : α → ℂ) (hinv : ∀ h : H, ∀ x, f (h.val • x) = f x)

omit [Countable G] [MeasurableSpace α] in
theorem orbitVector_norm_sq (x : α) :
    ‖orbitVector H f hinv x‖^2 = ∑ q : G ⧸ H, ‖f (q.out⁻¹ • x)‖^2 := by
  have hv : HasSum (fun q : Classes H => ‖orbitVector H f hinv x q‖^2)
      (‖orbitVector H f hinv x‖^2) := by
    simpa using lp.hasSum_norm (p := 2) (by norm_num) (orbitVector H f hinv x)
  rw [← hv.tsum_eq, tsum_fintype]
  have he := (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).sum_comp
    (fun q : G ⧸ H => ‖f (q.out⁻¹ • x)‖^2)
  convert he using 1
  apply Finset.sum_congr rfl
  intro q _
  rw [orbitVector_apply, orbitValue, QuantitativeMaass.CosetTrace.value_out]

include hmp hσ hnσ in
/-- Exact finite-cover norm unfolding for the actual orbit vector, valid
without any integrability assumption and hence ready for monotone inequalities. -/
theorem orbitVector_energy (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (‖orbitVector H f hinv x‖^2)
      ∂μ.withDensity (extensionDensity H σ)) =
    ∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ.withDensity σ := by
  simp_rw [orbitVector_norm_sq H f hinv,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  rw [lintegral_finsetSum (μ := μ.withDensity (extensionDensity H σ))
    (f := fun q : G ⧸ H => fun x => ENNReal.ofReal (‖f (q.out⁻¹ • x)‖^2))
    Finset.univ (fun q _ =>
      ENNReal.measurable_ofReal.comp ((hf.comp (hmp q.out⁻¹).measurable).norm.pow_const 2))]
  exact QuantitativeMaass.CosetTrace.sum_lintegral_translate μ hmp H
    (extensionDensity H σ) σ (extensionDensity_measurable H σ hσ) hσ
    (extensionDensity_normalized H σ hnσ) hnσ
    (fun x => ENNReal.ofReal (‖f x‖^2)) (by fun_prop)
    (by intro h x; rw [hinv])

#print axioms orbitVector_norm_sq
#print axioms orbitVector_energy
end QuantitativeEulerOldProjectionPhysical
