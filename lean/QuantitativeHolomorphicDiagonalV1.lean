module

public import QuantitativeHolomorphicPeriodizationV1
public import QuantitativeHolomorphicBergmanV1
public import QuantitativeHolomorphicSublevelV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane AsymptoticBergmanDecay AsymptoticUnweightedKernel
open MeasureTheory

/-- A quantitative diagonal estimate for the full periodized kernel.
Only the zero translation contributes the exact identity term. -/
theorem periodized_diagonal_error_bound (h : ℕ) {Y H : ℝ} (hY : 0 < Y) (hH : 0 < H)
    (z : ℍ) (hYz : Y ≤ z.im) (hHz : z.im ≤ H) :
    ‖(∑' n : ℤ, base (translate z n) z ^ (2 * h + 2)) - 1‖ ≤
      compactKernelBound Y H 0 / (1 + (h : ℝ) / (4 * H ^ 2)) := by
  let A : ℝ := (compactBaseBound Y H 0) ^ 2 / (1 + (h : ℝ) / (4 * H ^ 2))
  have hbound (n : ℤ) :
      ‖if n = 0 then (0 : ℂ) else base (translate z n) z ^ (2 * h + 2)‖ ≤ A * integerDecay n := by
    by_cases hn : n = 0
    · simp only [ite_eq_left hn, norm_zero]
      dsimp [A, integerDecay]
      positivity
    · rw [ite_eq_right hn, norm_pow, pow_add]
      have hdist : 1 ≤ ‖(translate z n : ℂ) - (z : ℂ)‖ := by
        simpa only [translate, add_sub_cancel_left] using int_complex_norm_ge_one n hn
      have him : (translate z n).im = z.im := by
        simp only [translate, UpperHalfPlane.im, Complex.add_im, Complex.intCast_im, add_zero]
      have hheight : (translate z n).im * z.im ≤ H ^ 2 := by
        rw [him]
        nlinarith [sq_nonneg (H - z.im)]
      have hp := bergman_even_power_bound (translate z n) z (by norm_num : (0 : ℝ) ≤ 1)
        hH hdist hheight h
      have hs := translated_base_square_bound (R := 0) hY z z hYz hYz hHz hHz (by simp) n
      calc
        _ ≤ (1 / (1 + (h : ℝ) * 1 ^ 2 / (4 * H ^ 2))) *
            ((compactBaseBound Y H 0) ^ 2 * integerDecay n) :=
          mul_le_mul hp hs (by positivity) (by positivity)
        _ = A * integerDecay n := by dsimp [A]; ring
  have hm : Summable (fun n : ℤ => A * integerDecay n) := integerDecay_summable.mul_left A
  have hs := Summable.of_norm_bounded hm hbound
  have htail : ‖∑' n : ℤ, if n = 0 then (0 : ℂ) else base (translate z n) z ^ (2 * h + 2)‖ ≤
      compactKernelBound Y H 0 / (1 + (h : ℝ) / (4 * H ^ 2)) := by
    apply (norm_tsum_le_tsum_norm hs.norm).trans
    apply (hs.norm.tsum_le_tsum hbound hm).trans_eq
    rw [tsum_mul_left]
    dsimp [A, compactKernelBound]
    ring
  have he := (translated_base_power_summable h z z).tsum_eq_add_tsum_ite 0
  have hz0 : translate z 0 = z := by apply UpperHalfPlane.ext; simp [translate]
  rw [hz0, base_self, one_pow] at he
  rw [he, add_sub_cancel_left]
  exact htail

theorem periodized_diagonal_integral_error_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (z : α → ℍ) (hz : Measurable z) (coeff : α → ℂ)
    (hcmeas : AEStronglyMeasurable coeff μ) (hc : ∀ᵐ x ∂μ, ‖coeff x‖ ≤ 1)
    (h : ℕ) {Y H : ℝ} (hY : 0 < Y) (hH : 0 < H)
    (hregion : ∀ᵐ x ∂μ, Y ≤ (z x).im ∧ (z x).im ≤ H) :
    ‖(∫ x, coeff x * (∑' n : ℤ, base (translate (z x) n) (z x) ^ (2 * h + 2)) ∂μ) -
        ∫ x, coeff x ∂μ‖ ≤
      (compactKernelBound Y H 0 / (1 + (h : ℝ) / (4 * H ^ 2))) * μ.real Set.univ := by
  let f : α → ℂ := fun x => coeff x * (∑' n : ℤ, base (translate (z x) n) (z x) ^ (2 * h + 2))
  have hfmeas : AEStronglyMeasurable f μ :=
    hcmeas.mul (periodized_kernel_measurable h z z hz hz).aestronglyMeasurable
  have hfbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ compactKernelBound Y H 0 := by
    filter_upwards [hc, hregion] with x hcx hx
    dsimp [f]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hcx).trans
      (periodized_kernel_norm_bound (R := 0) h hY (z x) (z x) hx.1 hx.1 hx.2 hx.2 (by simp))
  have hfi := Integrable.of_bound hfmeas _ hfbound
  have hci := Integrable.of_bound hcmeas 1 hc
  change ‖(∫ x, f x ∂μ) - ∫ x, coeff x ∂μ‖ ≤ _
  rw [← integral_sub hfi hci]
  have htail : ∀ᵐ x ∂μ, ‖f x - coeff x‖ ≤
      compactKernelBound Y H 0 / (1 + (h : ℝ) / (4 * H ^ 2)) := by
    filter_upwards [hc, hregion] with x hcx hx
    have he : f x - coeff x = coeff x *
        ((∑' n : ℤ, base (translate (z x) n) (z x) ^ (2 * h + 2)) - 1) := by dsimp [f]; ring
    rw [he, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hcx).trans
      (periodized_diagonal_error_bound h hY hH (z x) hx.1 hx.2)
  have hh := norm_integral_le_of_norm_le (integrable_const
    (compactKernelBound Y H 0 / (1 + (h : ℝ) / (4 * H ^ 2)))) htail
  simpa only [integral_const, smul_eq_mul, mul_comm (μ.real Set.univ)] using hh

theorem periodized_diagonal_integral_error_bound_of_cap
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (z : α → ℍ) (hz : Measurable z) (coeff : α → ℂ)
    (hcmeas : AEStronglyMeasurable coeff μ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ᵐ x ∂μ, ‖coeff x‖ ≤ C)
    (h : ℕ) {Y H : ℝ} (hY : 0 < Y) (hH : 0 < H)
    (hregion : ∀ᵐ x ∂μ, Y ≤ (z x).im ∧ (z x).im ≤ H) :
    ‖(∫ x, coeff x * (∑' n : ℤ, base (translate (z x) n) (z x) ^ (2 * h + 2)) ∂μ) -
        ∫ x, coeff x ∂μ‖ ≤
      C * (compactKernelBound Y H 0 / (1 + (h : ℝ) / (4 * H ^ 2))) * μ.real Set.univ := by
  let f : α → ℂ := fun x => coeff x * (∑' n : ℤ, base (translate (z x) n) (z x) ^ (2 * h + 2))
  have hfmeas : AEStronglyMeasurable f μ :=
    hcmeas.mul (periodized_kernel_measurable h z z hz hz).aestronglyMeasurable
  have hfbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C * compactKernelBound Y H 0 := by
    filter_upwards [hc, hregion] with x hcx hx
    dsimp [f]
    rw [norm_mul]
    exact mul_le_mul hcx
      (periodized_kernel_norm_bound (R := 0) h hY (z x) (z x) hx.1 hx.1 hx.2 hx.2 (by simp))
      (norm_nonneg _) hC
  have hfi := Integrable.of_bound hfmeas _ hfbound
  have hci := Integrable.of_bound hcmeas C hc
  change ‖(∫ x, f x ∂μ) - ∫ x, coeff x ∂μ‖ ≤ _
  rw [← integral_sub hfi hci]
  have htail : ∀ᵐ x ∂μ, ‖f x - coeff x‖ ≤
      C * (compactKernelBound Y H 0 / (1 + (h : ℝ) / (4 * H ^ 2))) := by
    filter_upwards [hc, hregion] with x hcx hx
    have he : f x - coeff x = coeff x *
        ((∑' n : ℤ, base (translate (z x) n) (z x) ^ (2 * h + 2)) - 1) := by dsimp [f]; ring
    rw [he, norm_mul]
    exact mul_le_mul hcx (periodized_diagonal_error_bound h hY hH (z x) hx.1 hx.2)
      (norm_nonneg _) hC
  have hh := norm_integral_le_of_norm_le (integrable_const
    (C * (compactKernelBound Y H 0 / (1 + (h : ℝ) / (4 * H ^ 2))))) htail
  simpa only [integral_const, smul_eq_mul, mul_comm (μ.real Set.univ)] using hh


#print axioms periodized_diagonal_error_bound
#print axioms periodized_diagonal_integral_error_bound

end QuantitativeHolomorphic
