module

public import FinitenessPaper2EulerLimitsV1
public import FinitenessAllLevelDiskSeriesV1

set_option autoImplicit false

public section

namespace FinitenessPaper2

open Filter FinitenessOriginalFourier FinitenessAllLevelDiskSeries
open scoped Topology

/-- A single integer polynomial envelope controls the normalized Fourier
coefficients of every member of the coefficient closure. -/
theorem closure_fullCoefficients_envelope (N k : ℕ) (σ : ℝ) (hN : 0 < N) :
    ∃ d : ℕ, ∀ f ∈ closure (E N k σ), ∀ n : ℕ,
      ‖fullCoefficients f k n‖ ≤ (n : ℝ)^d := by
  obtain ⟨d, hd⟩ := exists_nat_ge (σ+1+FinitenessCompletedNormalization.alpha k)
  refine ⟨d, ?_⟩
  intro f hf n
  by_cases hn : n = 0
  · subst n
    rw [fullCoefficients_zero (closure_zero hf), norm_zero]
    positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hb := closure_subset_coefficientBox hN hf n
  have hdcard : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
  have hbase : ‖f n‖ ≤ (n : ℝ)^(σ+1) := by
    calc
      ‖f n‖ ≤ (n.divisors.card : ℝ)*(n : ℝ)^σ := hb
      _ ≤ (n : ℝ)*(n : ℝ)^σ := mul_le_mul_of_nonneg_right hdcard (Real.rpow_nonneg hn'.le σ)
      _ = (n : ℝ)^(σ+1) := by rw [Real.rpow_add hn', Real.rpow_one]; ring
  have hnα := Real.rpow_pos_of_pos hn' (FinitenessCompletedNormalization.alpha k)
  calc
    ‖fullCoefficients f k n‖ = ‖f n‖*(n : ℝ)^(FinitenessCompletedNormalization.alpha k) := by
      simp only [fullCoefficients, FinitenessGrowthNormalization.normalized,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnα]
    _ ≤ (n : ℝ)^(σ+1)*(n : ℝ)^(FinitenessCompletedNormalization.alpha k) :=
      mul_le_mul_of_nonneg_right hbase hnα.le
    _ = (n : ℝ)^(σ+1+FinitenessCompletedNormalization.alpha k) := (Real.rpow_add hn' _ _).symm
    _ ≤ (n : ℝ)^d := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hn1 hd

/-- The actual normalized Fourier series converge in the Banach supremum
norm on every closed disk strictly inside the unit disk. -/
theorem fourier_disk_tendsto {N k : ℕ} {σ R : ℝ}
    (hN : 0 < N) (hR : 0 ≤ R) (hR1 : R < 1)
    {a : ℕ → ℕ → ℂ} {f : ℕ → ℂ} (ha : ∀ j, a j ∈ E N k σ)
    (ht : ∀ n, Tendsto (fun j => a j n) atTop (𝓝 (f n))) :
    Tendsto (fun j => diskSeries (fullCoefficients (a j) k) R) atTop
      (𝓝 (diskSeries (fullCoefficients f k) R)) := by
  obtain ⟨d, hd⟩ := closure_fullCoefficients_envelope N k σ hN
  apply diskSeries_tendsto_of_polynomial hR hR1 d
    (fun j n => hd (a j) (subset_closure (ha j)) n)
  intro n
  exact (ht n).mul_const (((n : ℝ)^(FinitenessCompletedNormalization.alpha k) : ℝ) : ℂ)

/-- The disk Banach-space sum is literally the existing Fourier disk
function, so the norm convergence concerns the intended analytic functions. -/
theorem closure_diskSeries_eq {N k : ℕ} {σ R : ℝ} {f : ℕ → ℂ}
    (hN : 0 < N) (hR : 0 ≤ R) (hR1 : R < 1)
    (hf : f ∈ closure (E N k σ)) (z : Disk R) :
    diskSeries (fullCoefficients f k) R z =
      FinitenessPolynomialSeries.sum (fullCoefficients f k) z.val := by
  obtain ⟨d, hd⟩ := closure_fullCoefficients_envelope N k σ hN
  rw [FinitenessPolynomialSeries.sum_eq_tsum]
  apply diskSeries_apply hR (fun n => pow_nonneg (Nat.cast_nonneg n) d) (hd f hf)
  exact summable_pow_mul_geometric_of_norm_lt_one d
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hR] using hR1)

#print axioms closure_fullCoefficients_envelope
#print axioms fourier_disk_tendsto
#print axioms closure_diskSeries_eq

end FinitenessPaper2
