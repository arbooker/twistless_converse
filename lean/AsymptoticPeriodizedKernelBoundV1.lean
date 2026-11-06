module

public import AsymptoticPeriodizedKernelLimitV1
public import Mathlib.Analysis.PSeries

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open UpperHalfPlane AsymptoticBergmanDecay

noncomputable def integerDecay (n : ℤ) : ℝ := 1 / (1 + |(n : ℝ)|)^2

theorem integerDecay_summable : Summable integerDecay := by
  have hs : Summable (fun n : ℕ => 1 / ((n+1 : ℕ) : ℝ)^2) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  rw [summable_int_iff_summable_nat_and_neg]
  constructor <;> simpa [integerDecay, add_comm] using hs

noncomputable def compactBaseBound (Y H R : ℝ) : ℝ :=
  2*H*(1+(R+1)/(2*Y))

theorem translated_base_bound {Y H R : ℝ} (hY : 0 < Y) (z u : ℍ)
    (hYz : Y ≤ z.im) (hYu : Y ≤ u.im) (hHz : z.im ≤ H) (hHu : u.im ≤ H)
    (hR : |z.re-u.re| ≤ R) (n : ℤ) :
    ‖base (translate z n) u‖ ≤ compactBaseBound Y H R / (1+|(n : ℝ)|) := by
  let D : ℂ := (z : ℂ)-star (u : ℂ)+n
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hR
  have hH : 0 < H := z.im_pos.trans_le hHz
  have hi : 2*Y ≤ ‖D‖ := by
    have hh := Complex.abs_im_le_norm D
    have hdi : D.im = z.im+u.im := by simp [D]
    rw [hdi, abs_of_pos (add_pos z.im_pos u.im_pos)] at hh
    linarith
  have hD : 0 < ‖D‖ := (by positivity : 0 < 2*Y).trans_le hi
  have hn : |(n : ℝ)| ≤ ‖D‖+R := by
    have he : (n : ℝ) = D.re-(z.re-u.re) := by simp [D]
    rw [he]
    exact (abs_sub _ _).trans (add_le_add (Complex.abs_re_le_norm D) hR)
  have hratio : 1+|(n : ℝ)| ≤ ‖D‖*(1+(R+1)/(2*Y)) := by
    have hh := mul_le_mul_of_nonneg_right hi
      (div_nonneg (by linarith : 0 ≤ R+1) (by positivity : 0 ≤ 2*Y))
    have he : (2*Y)*((R+1)/(2*Y))=R+1 := by field_simp
    rw [he] at hh
    nlinarith
  have hsqrt : Real.sqrt (z.im*u.im) ≤ H := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hH.le, by nlinarith [mul_le_mul hHz hHu u.im_pos.le hH.le]⟩
  have he : ‖base (translate z n) u‖ = 2*Real.sqrt (z.im*u.im)/‖D‖ := by
    rw [base_translate, norm_div]
    simp [D, Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [he]
  apply (div_le_div_iff₀ hD (by positivity : 0 < 1+|(n : ℝ)|)).mpr
  calc
    _ ≤ 2*H*(1+|(n : ℝ)|) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ 2*H*(‖D‖*(1+(R+1)/(2*Y))) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by unfold compactBaseBound; ring

theorem translated_base_square_bound {Y H R : ℝ} (hY : 0 < Y) (z u : ℍ)
    (hYz : Y ≤ z.im) (hYu : Y ≤ u.im) (hHz : z.im ≤ H) (hHu : u.im ≤ H)
    (hR : |z.re-u.re| ≤ R) (n : ℤ) :
    ‖base (translate z n) u‖^2 ≤ (compactBaseBound Y H R)^2 * integerDecay n := by
  apply (pow_le_pow_left₀ (norm_nonneg _)
    (translated_base_bound hY z u hYz hYu hHz hHu hR n) 2).trans_eq
  rw [div_pow]
  unfold integerDecay
  ring

noncomputable def compactKernelBound (Y H R : ℝ) : ℝ :=
  (compactBaseBound Y H R)^2 * ∑' n : ℤ, integerDecay n

/-- A common summable majorant for the full periodized kernel on the
retained region, uniform in the holomorphic weight. -/
theorem periodized_kernel_norm_bound (h : ℕ) {Y H R : ℝ} (hY : 0 < Y) (z u : ℍ)
    (hYz : Y ≤ z.im) (hYu : Y ≤ u.im) (hHz : z.im ≤ H) (hHu : u.im ≤ H)
    (hR : |z.re-u.re| ≤ R) :
    ‖∑' n : ℤ, base (translate z n) u^(2*h+2)‖ ≤ compactKernelBound Y H R := by
  have hs := (translated_base_power_summable h z u).norm
  apply (norm_tsum_le_tsum_norm hs).trans
  apply (hs.tsum_le_tsum (g:=fun n => (compactBaseBound Y H R)^2 * integerDecay n)
    (fun n => ?_) (integerDecay_summable.mul_left _)).trans_eq
  · rw [tsum_mul_left]
    rfl
  · rw [norm_pow]
    exact (pow_le_pow_of_le_one (norm_nonneg _) (norm_base_le_one _ _) (by omega)).trans
      (translated_base_square_bound hY z u hYz hYu hHz hHu hR n)

#print axioms translated_base_bound
#print axioms periodized_kernel_norm_bound

end AsymptoticUnweightedKernel
