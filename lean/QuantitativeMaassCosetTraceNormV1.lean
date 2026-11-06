module

public import QuantitativeMaassCosetTraceV1

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
/-- Exact unfolding of nonnegative coset integrals, valid even when infinite. -/
theorem sum_lintegral_translate (F : α → ℝ≥0∞) (hF : Measurable F)
    (hFinv : ∀ h : H, ∀ x, F (h.val • x) = F x) :
    (∑ q : G ⧸ H, ∫⁻ x, F (q.out⁻¹ • x) ∂μ.withDensity ρ) =
      ∫⁻ x, F x ∂μ.withDensity σ := by
  have hi := AsymptoticOrbitDensity.lintegral_invariant_eq μ (fun h : H => hmp h.val)
    (AsymptoticOrbitDensity.inducedDensity H ρ) σ
    (AsymptoticOrbitDensity.inducedDensity_measurable H ρ μ hmp hρ) hσ
    (AsymptoticOrbitDensity.inducedDensity_normalized H ρ hnρ) hnσ F hF hFinv
  rw [← hi, lintegral_withDensity_eq_lintegral_mul μ
    (AsymptoticOrbitDensity.inducedDensity_measurable H ρ μ hmp hρ) hF]
  simp only [Pi.mul_apply, AsymptoticOrbitDensity.inducedDensity, tsum_fintype,
    Finset.sum_mul]
  rw [lintegral_finsetSum (μ := μ) (f := fun q : G ⧸ H => fun x => ρ (q.out • x) * F x)
    Finset.univ (fun q _ => (hρ.comp (hmp q.out).measurable).mul hF)]
  apply Finset.sum_congr rfl
  intro q _
  rw [AsymptoticOrbitDensity.lintegral_translate_density μ hmp ρ hρ q.out F hF]
  exact lintegral_withDensity_eq_lintegral_mul μ
    (show Measurable (fun x => ρ (q.out • x)) from hρ.comp (hmp q.out).measurable) hF

include hmp hρ hσ hnρ hnσ in
theorem branch_eLpNorm_le (f : α → ℂ) (hf : Measurable f)
    (hinv : ∀ h : H, ∀ x, f (h.val • x) = f x) (q : G ⧸ H) :
    eLpNorm (fun x => f (q.out⁻¹ • x)) 2 (μ.withDensity ρ) ≤
      eLpNorm f 2 (μ.withDensity σ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (μ := μ.withDensity ρ)
      (f := fun x => f (q.out⁻¹ • x)) (by norm_num) (by norm_num)
      (hf.comp (hmp q.out⁻¹).measurable).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (μ := μ.withDensity σ)
      (f := f) (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  have hi := sum_lintegral_translate μ hmp H ρ σ hρ hσ hnρ hnσ
    (fun x => ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal) (by fun_prop) (by intro h x; rw [hinv])
  rw [← hi]
  exact Finset.single_le_sum
    (f := fun q : G ⧸ H => ∫⁻ x, ‖f (q.out⁻¹ • x)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ.withDensity ρ)
    (fun _ _ => zero_le) (Finset.mem_univ q)

include hmp hρ hσ hnρ hnσ in
theorem trace_memLp (f : α → ℂ) (hf : Measurable f)
    (hinv : ∀ h : H, ∀ x, f (h.val • x) = f x) (hfL : MemLp f 2 (μ.withDensity σ)) :
    MemLp (trace H f hinv) 2 (μ.withDensity ρ) := by
  rw [show trace H f hinv = (fun x => ∑ q : G ⧸ H, f (q.out⁻¹ • x)) from
    funext (trace_out H f hinv)]
  apply memLp_finsetSum
  intro q _
  exact (branch_eLpNorm_le μ hmp H ρ σ hρ hσ hnρ hnσ f hf hinv q).trans_lt hfL

include hmp hρ hσ hnρ hnσ in
/-- A direct finite-coset L² bound before using the sharper adjoint identity. -/
theorem trace_eLpNorm_le (f : α → ℂ) (hf : Measurable f)
    (hinv : ∀ h : H, ∀ x, f (h.val • x) = f x) :
    eLpNorm (trace H f hinv) 2 (μ.withDensity ρ) ≤
      (Fintype.card (G ⧸ H) : ℝ≥0∞) * eLpNorm f 2 (μ.withDensity σ) := by
  have he : trace H f hinv = ∑ q : G ⧸ H, (fun x => f (q.out⁻¹ • x)) := by
    funext x
    simp only [trace_out, Finset.sum_apply]
  rw [he]
  calc
    _ ≤ ∑ q : G ⧸ H, eLpNorm (fun x => f (q.out⁻¹ • x)) 2 (μ.withDensity ρ) :=
      eLpNorm_sum_le (by norm_num)
    _ ≤ ∑ _q : G ⧸ H, eLpNorm f 2 (μ.withDensity σ) :=
      Finset.sum_le_sum (fun q _ => branch_eLpNorm_le μ hmp H ρ σ hρ hσ hnρ hnσ f hf hinv q)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

#print axioms sum_lintegral_translate
#print axioms trace_memLp
#print axioms trace_eLpNorm_le

end QuantitativeMaass.CosetTrace
