module

public import AsymptoticPeriodizedKernelBoundV1
public import AsymptoticPeriodizedKernelIntegralV1
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane AsymptoticBergmanDecay AsymptoticUnweightedKernel

/-- Outside a fixed finite range of translations the entire
periodization tail is exponentially small, uniformly on the retained
height/real-displacement region.  This uses the actual periodized
Bergman base and the summable square bound already proved in the
qualitative development. -/
theorem periodization_tail_bound (h : ℕ) {Y H R : ℝ} (hY : 0 < Y) (z u : ℍ)
    (hYz : Y ≤ z.im) (hYu : Y ≤ u.im) (hHz : z.im ≤ H) (hHu : u.im ≤ H)
    (hR : |z.re - u.re| ≤ R) (S : Finset ℤ)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H R ≤ 1 + |(n : ℝ)|) :
    ‖∑' n : ℤ, if n ∈ S then (0 : ℂ) else base (translate z n) u ^ (2 * h + 2)‖ ≤
      (1 / 2 : ℝ) ^ (2 * h) * compactKernelBound Y H R := by
  classical
  let K := compactBaseBound Y H R
  let A := (1 / 2 : ℝ) ^ (2 * h) * K ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbound (n : ℤ) :
      ‖if n ∈ S then (0 : ℂ) else base (translate z n) u ^ (2 * h + 2)‖ ≤ A * integerDecay n := by
    by_cases hn : n ∈ S
    · simp only [ite_eq_left hn, norm_zero]
      exact mul_nonneg hA (by unfold integerDecay; positivity)
    · rw [ite_eq_right hn, norm_pow]
      have hb := translated_base_bound hY z u hYz hYu hHz hHu hR n
      have hhalf : ‖base (translate z n) u‖ ≤ (1 / 2 : ℝ) := by
        apply hb.trans
        apply (div_le_iff₀ (by positivity : 0 < 1 + |(n : ℝ)|)).mpr
        linarith [hfar n hn]
      have hs := translated_base_square_bound hY z u hYz hYu hHz hHu hR n
      rw [pow_add]
      calc
        _ ≤ (1 / 2 : ℝ) ^ (2 * h) * (K ^ 2 * integerDecay n) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hhalf (2 * h)) hs
            (by positivity) (by positivity)
        _ = A * integerDecay n := by dsimp [A]; ring
  have hm : Summable (fun n : ℤ => A * integerDecay n) := integerDecay_summable.mul_left A
  have hs := Summable.of_norm_bounded hm hbound
  calc
    _ ≤ ∑' n : ℤ, ‖if n ∈ S then (0 : ℂ) else base (translate z n) u ^ (2 * h + 2)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℤ, A * integerDecay n := hs.norm.tsum_le_tsum hbound hm
    _ = _ := by
      rw [tsum_mul_left]
      dsimp [A, K, compactKernelBound]
      ring

theorem periodization_truncation_bound (h : ℕ) {Y H R : ℝ} (hY : 0 < Y) (z u : ℍ)
    (hYz : Y ≤ z.im) (hYu : Y ≤ u.im) (hHz : z.im ≤ H) (hHu : u.im ≤ H)
    (hR : |z.re - u.re| ≤ R) (S : Finset ℤ)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H R ≤ 1 + |(n : ℝ)|) :
    ‖(∑' n : ℤ, base (translate z n) u ^ (2 * h + 2)) -
        ∑ n ∈ S, base (translate z n) u ^ (2 * h + 2)‖ ≤
      (1 / 2 : ℝ) ^ (2 * h) * compactKernelBound Y H R := by
  classical
  have hs := translated_base_power_summable h z u
  have hhead : Summable (fun n : ℤ => if n ∈ S then base (translate z n) u ^ (2 * h + 2) else 0) := by
    apply summable_of_ne_finset_zero (s := S)
    intro n hn
    simp [hn]
  have hid : (fun n : ℤ => base (translate z n) u ^ (2 * h + 2) -
      (if n ∈ S then base (translate z n) u ^ (2 * h + 2) else 0)) =
      (fun n : ℤ => if n ∈ S then 0 else base (translate z n) u ^ (2 * h + 2)) := by
    funext n
    split_ifs <;> simp
  have he := hs.tsum_sub hhead
  rw [hid] at he
  have hheadsum := sum_eq_tsum_indicator (fun n => base (translate z n) u ^ (2 * h + 2)) S
  simp only [Set.indicator_apply, Finset.mem_coe] at hheadsum
  rw [← hheadsum] at he
  rw [← he]
  exact periodization_tail_bound h hY z u hYz hYu hHz hHu hR S hfar

/-- The pointwise tail estimate passes to an actual branch integral,
including a bounded measurable phase that may depend on the weight. -/
theorem periodization_integral_truncation_bound
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (z u : α → ℍ) (hz : Measurable z) (hu : Measurable u) (c : α → ℂ)
    (hcmeas : MeasureTheory.AEStronglyMeasurable c μ)
    (hc : ∀ᵐ x ∂μ, ‖c x‖ ≤ 1) (h : ℕ) {Y H R : ℝ} (hY : 0 < Y)
    (hregion : ∀ᵐ x ∂μ, Y ≤ (z x).im ∧ Y ≤ (u x).im ∧ (z x).im ≤ H ∧
      (u x).im ≤ H ∧ |(z x).re - (u x).re| ≤ R)
    (S : Finset ℤ)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H R ≤ 1 + |(n : ℝ)|) :
    ‖(∫ x, c x * (∑' n : ℤ, base (translate (z x) n) (u x) ^ (2 * h + 2)) ∂μ) -
        ∫ x, c x * (∑ n ∈ S, base (translate (z x) n) (u x) ^ (2 * h + 2)) ∂μ‖ ≤
      ((1 / 2 : ℝ) ^ (2 * h) * compactKernelBound Y H R) * μ.real Set.univ := by
  classical
  let f : α → ℂ := fun x => c x * (∑' n : ℤ, base (translate (z x) n) (u x) ^ (2 * h + 2))
  let g : α → ℂ := fun x => c x * (∑ n ∈ S, base (translate (z x) n) (u x) ^ (2 * h + 2))
  have hfmeas : MeasureTheory.AEStronglyMeasurable f μ :=
    hcmeas.mul ((periodized_kernel_measurable h z u hz hu).aestronglyMeasurable)
  have hgmeas : MeasureTheory.AEStronglyMeasurable g μ := by
    apply hcmeas.mul
    apply Measurable.aestronglyMeasurable
    apply Finset.measurable_sum
    intro n _
    exact ((base_continuous.measurable.comp
      (((translate_continuous n).measurable.comp hz).prodMk hu)).pow_const (2 * h + 2))
  have hfbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ compactKernelBound Y H R := by
    filter_upwards [hc, hregion] with x hcx hx
    dsimp [f]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hcx).trans
      (periodized_kernel_norm_bound h hY (z x) (u x) hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2)
  have hgbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ (S.card : ℝ) := by
    filter_upwards [hc] with x hcx
    dsimp [g]
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) hcx).trans
    apply (norm_sum_le _ _).trans
    calc
      (∑ n ∈ S, ‖base (translate (z x) n) (u x) ^ (2 * h + 2)‖) ≤ ∑ _n ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (norm_base_le_one _ _)
      _ = _ := by simp
  have hfi := MeasureTheory.Integrable.of_bound hfmeas _ hfbound
  have hgi := MeasureTheory.Integrable.of_bound hgmeas _ hgbound
  change ‖(∫ x, f x ∂μ) - ∫ x, g x ∂μ‖ ≤ _
  rw [← MeasureTheory.integral_sub hfi hgi]
  have htail : ∀ᵐ x ∂μ, ‖f x - g x‖ ≤ (1 / 2 : ℝ) ^ (2 * h) * compactKernelBound Y H R := by
    filter_upwards [hc, hregion] with x hcx hx
    dsimp [f, g]
    rw [← mul_sub, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hcx).trans
      (periodization_truncation_bound h hY (z x) (u x)
        hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2 S hfar)
  have hh := MeasureTheory.norm_integral_le_of_norm_le (MeasureTheory.integrable_const
    ((1 / 2 : ℝ) ^ (2 * h) * compactKernelBound Y H R)) htail
  simpa only [MeasureTheory.integral_const, smul_eq_mul, mul_comm (μ.real Set.univ)] using hh

#print axioms periodization_tail_bound
#print axioms periodization_truncation_bound
#print axioms periodization_integral_truncation_bound

end QuantitativeHolomorphic
