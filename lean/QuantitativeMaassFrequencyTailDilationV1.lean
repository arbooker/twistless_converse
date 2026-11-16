module

public import QuantitativeMaassPositiveFrequencyTailV1
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace QuantitativeMaass

/-- Nonnegative integrals under a positive real dilation, including
infinite values. -/
theorem lintegral_positive_dilation (f : ℝ→ℝ≥0∞) (a : ℝ) (ha : 0<a) :
    (∫⁻ x,f (a*x))=ENNReal.ofReal a⁻¹*(∫⁻ x,f x) := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.smul (isUnit_iff_ne_zero.mpr ha.ne').unit).toMeasurableEquiv
  have hh := lintegral_map_equiv (μ := (volume : Measure ℝ)) f e
  change (∫⁻ x,f x ∂Measure.map (fun x : ℝ => a • x) volume)=∫⁻ x,f (a*x) at hh
  rw [Measure.map_addHaar_smul volume ha.ne',lintegral_smul_measure] at hh
  simpa only [Module.finrank_self,pow_one,abs_of_pos (inv_pos.mpr ha),smul_eq_mul] using hh.symm

/-- The logarithmic height measure dy/y has no dilation factor. -/
theorem lintegral_frequency_tail_dilation (h : ℝ→ℝ≥0∞) (H a : ℝ) (hH : 0<H) (ha : 0<a) :
    (∫⁻ y in Ici H,h (a*y)/ENNReal.ofReal y)=
      ∫⁻ u in Ici (a*H),h u/ENNReal.ofReal u := by
  let g := (Ici (a*H)).indicator (fun u => h u/ENNReal.ofReal u)
  have hpoint (y : ℝ) : g (a*y)=ENNReal.ofReal a⁻¹*
      (Ici H).indicator (fun y => h (a*y)/ENNReal.ofReal y) y := by
    classical
    by_cases hy : H≤y
    · have hy0 : 0<y := hH.trans_le hy
      have hay : a*H≤a*y := mul_le_mul_of_nonneg_left hy ha.le
      have hi : (ENNReal.ofReal (a*y))⁻¹=
          ENNReal.ofReal a⁻¹*(ENNReal.ofReal y)⁻¹ := by
        rw [←ENNReal.ofReal_inv_of_pos (mul_pos ha hy0),mul_inv_rev,
          ENNReal.ofReal_mul (inv_nonneg.mpr hy0.le),ENNReal.ofReal_inv_of_pos hy0]
        ac_rfl
      dsimp only [g]
      rw [Set.indicator_of_mem (show a*y∈Ici (a*H) from hay),
        Set.indicator_of_mem (show y∈Ici H from hy),div_eq_mul_inv,hi,div_eq_mul_inv]
      ac_rfl
    · have hay : ¬a*H≤a*y := by exact fun hh => hy ((mul_le_mul_iff_right₀ ha).mp hh)
      dsimp only [g]
      rw [Set.indicator_of_notMem (show a*y∉Ici (a*H) from hay),
        Set.indicator_of_notMem (show y∉Ici H from hy),mul_zero]
  have hh := lintegral_positive_dilation g a ha
  simp_rw [hpoint] at hh
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator measurableSet_Ici] at hh
  change ENNReal.ofReal a⁻¹*(∫⁻ y in Ici H,h (a*y)/ENNReal.ofReal y)=
    ENNReal.ofReal a⁻¹*(∫⁻ u,(Ici (a*H)).indicator (fun u => h u/ENNReal.ofReal u) u) at hh
  rw [lintegral_indicator measurableSet_Ici] at hh
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr (inv_pos.mpr ha)).ne' ENNReal.ofReal_ne_top).mp hh

/-- Summing all positive nonzero Fourier modes above height H costs at
most H inverse times the total positive-frequency mass. -/
theorem positive_frequency_height_tail (h : ℝ→ℝ≥0∞) (hm : Measurable h)
    (H : ℝ) (hH : 0<H) :
    (∫⁻ y in Ici H,∑' n : ℕ,h (((n+1:ℕ):ℝ)*y)/ENNReal.ofReal y)≤
      ENNReal.ofReal H⁻¹*(∫⁻ u in Ioi (0:ℝ),h u) := by
  have hmF (n : ℕ) : Measurable (fun y : ℝ => h (((n+1:ℕ):ℝ)*y)/ENNReal.ofReal y) := by
    fun_prop
  rw [lintegral_tsum (fun n => (hmF n).aemeasurable)]
  have hd (n : ℕ) :
      (∫⁻ y in Ici H,h (((n+1:ℕ):ℝ)*y)/ENNReal.ofReal y)=
      ∫⁻ u in Ici (((n+1:ℕ):ℝ)*H),h u/ENNReal.ofReal u :=
    lintegral_frequency_tail_dilation h H ((n+1:ℕ):ℝ) hH (by positivity)
  simp_rw [hd]
  have he (n : ℕ) :
      (∫⁻ u in Ici (((n+1:ℕ):ℝ)*H),h u/ENNReal.ofReal u)=
      ∫⁻ u in Ioi (0:ℝ),(Ici (((n+1:ℕ):ℝ)*H)).indicator (fun u => h u/ENNReal.ofReal u) u := by
    rw [lintegral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.mpr]
    intro u hu
    exact lt_of_lt_of_le (mul_pos (by positivity) hH) hu
  simp_rw [he]
  have hmI (n : ℕ) : Measurable ((Ici (((n+1:ℕ):ℝ)*H)).indicator
      (fun u : ℝ => h u/ENNReal.ofReal u)) :=
    (hm.div measurable_id.ennreal_ofReal).indicator measurableSet_Ici
  rw [←lintegral_tsum (fun n => (hmI n).aemeasurable)]
  exact positive_frequency_tail_count H hH h

#print axioms lintegral_positive_dilation
#print axioms lintegral_frequency_tail_dilation
#print axioms positive_frequency_height_tail

end QuantitativeMaass
