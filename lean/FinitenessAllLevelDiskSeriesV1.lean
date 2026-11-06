module

public import FinitenessPolynomialSeriesV1
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false

@[expose] public noncomputable section

namespace FinitenessAllLevelDiskSeries

open Filter Metric
open scoped Topology

abbrev Disk (R : ℝ) := ↥(closedBall (0 : ℂ) R)

def monomial (R : ℝ) (n : ℕ) : C(Disk R, ℂ) :=
  ⟨fun z => z.val^n, continuous_subtype_val.pow n⟩

theorem norm_monomial_le {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ‖monomial R n‖ ≤ R^n := by
  apply (ContinuousMap.norm_le _ (pow_nonneg hR n)).mpr
  intro z
  change ‖z.val^n‖ ≤ R^n
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (by simpa only [mem_closedBall, dist_zero_right] using z.property) n

def diskSeries (a : ℕ → ℂ) (R : ℝ) : C(Disk R, ℂ) :=
  ∑' n : ℕ, a n • monomial R n

theorem term_norm_le {R : ℝ} (hR : 0 ≤ R) {a : ℕ → ℂ} {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (ha : ∀ n, ‖a n‖ ≤ b n) (n : ℕ) :
    ‖a n • monomial R n‖ ≤ b n*R^n := by
  rw [norm_smul]
  exact mul_le_mul (ha n) (norm_monomial_le hR n) (norm_nonneg _) (hb n)

theorem diskSeries_summable {R : ℝ} (hR : 0 ≤ R) {a : ℕ → ℂ} {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (ha : ∀ n, ‖a n‖ ≤ b n)
    (hs : Summable (fun n : ℕ => b n*R^n)) :
    Summable (fun n : ℕ => a n • monomial R n) :=
  hs.of_norm_bounded (term_norm_le hR hb ha)

/-- The Banach-space sum represents the actual scalar power series. -/
theorem diskSeries_apply {R : ℝ} (hR : 0 ≤ R) {a : ℕ → ℂ} {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (ha : ∀ n, ‖a n‖ ≤ b n)
    (hs : Summable (fun n : ℕ => b n*R^n)) (z : Disk R) :
    diskSeries a R z = ∑' n : ℕ, a n*z.val^n := by
  exact (ContinuousMap.evalCLM ℂ z).map_tsum (diskSeries_summable hR hb ha hs)

/-- Coefficientwise convergence under a common summable envelope implies
convergence in the supremum norm on the closed disk. -/
theorem diskSeries_tendsto {R : ℝ} (hR : 0 ≤ R)
    {a : ℕ → ℕ → ℂ} {f : ℕ → ℂ} {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (ha : ∀ j n, ‖a j n‖ ≤ b n)
    (hs : Summable (fun n : ℕ => b n*R^n))
    (ht : ∀ n, Tendsto (fun j => a j n) atTop (𝓝 (f n))) :
    Tendsto (fun j => diskSeries (a j) R) atTop (𝓝 (diskSeries f R)) := by
  apply tendsto_tsum_of_dominated_convergence hs
  · intro n
    exact (ht n).smul_const (monomial R n)
  · exact Filter.Eventually.of_forall (fun j n => term_norm_le hR hb (ha j) n)

/-- The polynomial envelope relevant for normalized Fourier coefficients
is summable on every strictly smaller disk. -/
theorem diskSeries_tendsto_of_polynomial {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1)
    {a : ℕ → ℕ → ℂ} {f : ℕ → ℂ} (d : ℕ)
    (ha : ∀ j n, ‖a j n‖ ≤ (n : ℝ)^d)
    (ht : ∀ n, Tendsto (fun j => a j n) atTop (𝓝 (f n))) :
    Tendsto (fun j => diskSeries (a j) R) atTop (𝓝 (diskSeries f R)) := by
  apply diskSeries_tendsto hR (fun n => pow_nonneg (Nat.cast_nonneg n) d) ha _ ht
  exact summable_pow_mul_geometric_of_norm_lt_one d
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hR] using hR1)

#print axioms diskSeries_apply
#print axioms diskSeries_tendsto
#print axioms diskSeries_tendsto_of_polynomial

end FinitenessAllLevelDiskSeries
