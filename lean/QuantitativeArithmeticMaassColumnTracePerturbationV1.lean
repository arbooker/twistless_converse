module

public import QuantitativeArithmeticMaassColumnRegionEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped ENNReal

namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Changing the column, rather than commuting its cutoff through an
operator, has a quantitative quadratic-form bound. -/
theorem column_quadratic_perturbation (T : H →L[ℂ] H) (c d : H)
    (δ : ℝ) (hδ : 0 < δ) :
    |(inner ℂ (T c) c).re-(inner ℂ (T d) d).re| ≤
      ‖T‖*(δ*‖d‖^2+(1+δ⁻¹)*‖c-d‖^2) := by
  have heq : inner ℂ (T c) c-inner ℂ (T d) d =
      inner ℂ (T (c-d)) c+inner ℂ (T d) (c-d) := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  have htri := norm_le_norm_sub_add c d
  have hy := two_mul_le_add_mul_sq (a := ‖d‖) (b := ‖c-d‖) hδ
  calc
    _ = |(inner ℂ (T c) c-inner ℂ (T d) d).re| := by rw [Complex.sub_re]
    _ ≤ ‖inner ℂ (T c) c-inner ℂ (T d) d‖ := Complex.abs_re_le_norm _
    _ ≤ ‖inner ℂ (T (c-d)) c‖+‖inner ℂ (T d) (c-d)‖ := by
      rw [heq]
      exact norm_add_le _ _
    _ ≤ ‖T (c-d)‖*‖c‖+‖T d‖*‖c-d‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ (‖T‖*‖c-d‖)*(‖c-d‖+‖d‖)+(‖T‖*‖d‖)*‖c-d‖ := by
      gcongr
      · exact T.le_opNorm _
      · exact T.le_opNorm _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hy (norm_nonneg T)]

/-- A tunable trace error for replacing a sharp column by a smoothed
column. A small collar-energy estimate can be inserted in the final term.
No commutation between the cutoff and T is required. -/
theorem columnLinearTrace_column_perturbation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c d : α → H) (hc : MemLp c 2 μ) (hd : MemLp d 2 μ)
    (T : H →L[ℂ] H) (δ : ℝ) (hδ : 0 < δ) :
    |columnLinearTrace μ c T-columnLinearTrace μ d T| ≤
      ‖T‖*(δ*(∫ x, ‖d x‖^2 ∂μ)+(1+δ⁻¹)*(∫ x, ‖c x-d x‖^2 ∂μ)) := by
  have hid := (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd
  have hie : Integrable (fun x => ‖c x-d x‖^2) μ := by
    simpa only [Pi.sub_apply] using
      (memLp_two_iff_integrable_sq_norm (hc.sub hd).aestronglyMeasurable).mp (hc.sub hd)
  simp only [columnLinearTrace]
  rw [← integral_sub (columnLinearTrace_integrable μ c hc T)
    (columnLinearTrace_integrable μ d hd T), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x, ‖T‖*(δ*‖d x‖^2+(1+δ⁻¹)*‖c x-d x‖^2) ∂μ := by
      apply norm_integral_le_of_norm_le (((hid.const_mul δ).add (hie.const_mul (1+δ⁻¹))).const_mul ‖T‖)
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs, Pi.add_apply] using column_quadratic_perturbation T (c x) (d x) δ hδ)
    _ = _ := by
      rw [integral_const_mul, integral_add (hid.const_mul δ) (hie.const_mul (1+δ⁻¹)),
        integral_const_mul, integral_const_mul]

#print axioms column_quadratic_perturbation
#print axioms columnLinearTrace_column_perturbation

end QuantitativeMaass
