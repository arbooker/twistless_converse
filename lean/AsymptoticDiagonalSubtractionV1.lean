module

public import AsymptoticDiagonalComparisonV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticDiagonalComparison

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

omit [InnerProductSpace ℂ G] in
theorem square_sub_le (u d : G) : ‖u-d‖^2 ≤ 2*‖u‖^2 + 2*‖d‖^2 := by
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le u d) 2
  nlinarith [sq_nonneg (‖u‖-‖d‖)]

omit [InnerProductSpace ℂ G] in
theorem square_sub_summable (u d : ℕ → G)
    (hu : Summable (fun n => ‖u n‖^2)) (hd : Summable (fun n => ‖d n‖^2)) :
    Summable (fun n => ‖u n-d n‖^2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => square_sub_le (u n) (d n))
    ((hu.mul_left 2).add (hd.mul_left 2))

theorem diagonal_subtract_bound (W : G →L[ℂ] G) (u d : G) :
    ‖(⟪W u,u⟫_ℂ).re - (⟪W (u-d),u-d⟫_ℂ).re‖ ≤
      ‖W‖ * (2*‖u‖*‖d‖ + ‖d‖^2) := by
  have hh := diagonal_sub_bound W u (u-d)
  rw [show u-(u-d)=d by abel] at hh
  apply hh.trans
  have hn := mul_le_mul_of_nonneg_left (norm_sub_le u d) (norm_nonneg d)
  apply (mul_le_mul_of_nonneg_left (add_le_add le_rfl hn) (norm_nonneg W)).trans_eq
  ring

/-- Removing a small square-summable part of the Fourier vectors costs
at most a cross term and its own diagonal mass. The bound does not require
positivity of the middle operator. -/
theorem trace_subtract_bound (W : G →L[ℂ] G) (u d : ℕ → G)
    (hu : Summable (fun n => ‖u n‖^2)) (hd : Summable (fun n => ‖d n‖^2))
    {U D : ℝ} (hU : (∑' n, ‖u n‖^2) ≤ U) (hD : (∑' n, ‖d n‖^2) ≤ D) :
    ‖(∑' n, (⟪W (u n),u n⟫_ℂ).re) -
      (∑' n, (⟪W (u n-d n),u n-d n⟫_ℂ).re)‖ ≤
        ‖W‖ * (2*Real.sqrt U*Real.sqrt D + D) := by
  have hv := square_sub_summable u d hu hd
  obtain ⟨hp, hp'⟩ := product_summable_bound (fun n => ‖u n‖) (fun n => ‖d n‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hu hd hU hD
  have hs := ((diagonal_summable W u hu).sub (diagonal_summable W (fun n => u n-d n) hv)).norm
  rw [← (diagonal_summable W u hu).tsum_sub (diagonal_summable W (fun n => u n-d n) hv)]
  apply (norm_tsum_le_tsum_norm hs).trans
  have hmaj : Summable (fun n => ‖W‖ * (2*‖u n‖*‖d n‖ + ‖d n‖^2)) := by
    simpa only [mul_assoc] using ((hp.mul_left 2).add hd).mul_left ‖W‖
  apply (hs.tsum_le_tsum (fun n => diagonal_subtract_bound W (u n) (d n)) hmaj).trans
  have he : (∑' n, (2*‖u n‖*‖d n‖ + ‖d n‖^2)) =
      2*(∑' n, ‖u n‖*‖d n‖) + ∑' n, ‖d n‖^2 := by
    simp only [mul_assoc]
    rw [(hp.mul_left 2).tsum_add hd, tsum_mul_left]
  rw [tsum_mul_left, he]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hh := add_le_add (mul_le_mul_of_nonneg_left hp' (by norm_num : (0 : ℝ) ≤ 2)) hD
  exact hh.trans_eq (by ring)

#print axioms square_sub_summable
#print axioms trace_subtract_bound

end AsymptoticDiagonalComparison
