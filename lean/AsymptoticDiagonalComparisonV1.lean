module

public import AsymptoticGramTracePerturbationV1
public import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
@[expose] public section

namespace AsymptoticDiagonalComparison

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct

theorem product_summable_bound (f g : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (hsf : Summable (fun n => (f n)^2)) (hsg : Summable (fun n => (g n)^2))
    {D S : ℝ} (hD : (∑' n, (f n)^2) ≤ D) (hS : (∑' n, (g n)^2) ≤ S) :
    Summable (fun n => f n*g n) ∧ (∑' n, f n*g n) ≤ Real.sqrt D * Real.sqrt S := by
  have hfin (I : Finset ℕ) : (∑ n ∈ I, f n*g n) ≤ Real.sqrt D * Real.sqrt S := by
    apply (Real.sum_mul_le_sqrt_mul_sqrt I f g).trans
    exact mul_le_mul
      (Real.sqrt_le_sqrt ((hsf.sum_le_tsum I (fun _ _ => sq_nonneg _)).trans hD))
      (Real.sqrt_le_sqrt ((hsg.sum_le_tsum I (fun _ _ => sq_nonneg _)).trans hS))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h0 : ∀ n, 0 ≤ f n*g n := fun n => mul_nonneg (hf n) (hg n)
  exact ⟨summable_of_sum_le h0 hfin, Real.tsum_le_of_sum_le h0 hfin⟩

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem diagonal_bound (W : G →L[ℂ] G) (u : G) :
    ‖(⟪W u,u⟫_ℂ).re‖ ≤ ‖W‖ * ‖u‖^2 := by
  rw [Real.norm_eq_abs]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_inner_le_norm _ _).trans
  apply (mul_le_mul_of_nonneg_right (W.le_opNorm _) (norm_nonneg _)).trans_eq
  ring

theorem diagonal_sub_bound (W : G →L[ℂ] G) (u v : G) :
    ‖(⟪W u,u⟫_ℂ).re - (⟪W v,v⟫_ℂ).re‖ ≤
      ‖W‖ * (‖u-v‖*‖u‖ + ‖u-v‖*‖v‖) := by
  have he : ⟪W u,u⟫_ℂ - ⟪W v,v⟫_ℂ =
      ⟪W (u-v),u⟫_ℂ + ⟪W v,u-v⟫_ℂ := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    abel
  rw [← Complex.sub_re, he, Real.norm_eq_abs]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_add_le _ _).trans
  have h1 := (norm_inner_le_norm (𝕜:=ℂ) (W (u-v)) u).trans
    (mul_le_mul_of_nonneg_right (W.le_opNorm _) (norm_nonneg _))
  have h2 := (norm_inner_le_norm (𝕜:=ℂ) (W v) (u-v)).trans
    (mul_le_mul_of_nonneg_right (W.le_opNorm _) (norm_nonneg _))
  apply (add_le_add h1 h2).trans_eq
  ring

theorem diagonal_summable (W : G →L[ℂ] G) (u : ℕ → G)
    (hu : Summable (fun n => ‖u n‖^2)) : Summable (fun n => (⟪W (u n),u n⟫_ℂ).re) :=
  Summable.of_norm_bounded (hu.mul_left ‖W‖) (fun n => diagonal_bound W (u n))

/-- Cauchy--Schwarz compares two summable diagonals directly. This avoids
introducing trace-class or Hilbert--Schmidt operators just to compare
localized holomorphic Fourier traces. -/
theorem trace_difference_bound (W : G →L[ℂ] G) (u v : ℕ → G)
    (hu : Summable (fun n => ‖u n‖^2)) (hv : Summable (fun n => ‖v n‖^2))
    (hd : Summable (fun n => ‖u n-v n‖^2)) {D U V : ℝ}
    (hD : (∑' n, ‖u n-v n‖^2) ≤ D) (hU : (∑' n, ‖u n‖^2) ≤ U)
    (hV : (∑' n, ‖v n‖^2) ≤ V) :
    ‖(∑' n, (⟪W (u n),u n⟫_ℂ).re) - (∑' n, (⟪W (v n),v n⟫_ℂ).re)‖ ≤
      ‖W‖ * Real.sqrt D * (Real.sqrt U + Real.sqrt V) := by
  obtain ⟨hdu, hdu'⟩ := product_summable_bound (fun n => ‖u n-v n‖) (fun n => ‖u n‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hd hu hD hU
  obtain ⟨hdv, hdv'⟩ := product_summable_bound (fun n => ‖u n-v n‖) (fun n => ‖v n‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hd hv hD hV
  have hsum := ((diagonal_summable W u hu).sub (diagonal_summable W v hv)).norm
  rw [← (diagonal_summable W u hu).tsum_sub (diagonal_summable W v hv)]
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply (hsum.tsum_le_tsum (fun n => diagonal_sub_bound W (u n) (v n))
    ((hdu.add hdv).mul_left ‖W‖)).trans
  rw [tsum_mul_left, hdu.tsum_add hdv]
  apply (mul_le_mul_of_nonneg_left (add_le_add hdu' hdv') (norm_nonneg _)).trans_eq
  ring

#print axioms product_summable_bound
#print axioms diagonal_sub_bound
#print axioms trace_difference_bound

end AsymptoticDiagonalComparison
