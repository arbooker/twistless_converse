module

public import MaassKBesselMomentsV1
public import MaassSqrtBoundaryV1

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace MaassKBessel

theorem zero_moment_nonneg (j : ℕ) (x : ℝ) : 0 ≤ moment j 0 x := by
  unfold moment
  apply integral_nonneg
  intro r
  simp only [zero_mul, Real.cos_zero, mul_one]
  positivity

theorem zero_moment_integrable (j : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun r : ℝ => Real.cosh r ^ j * Real.exp (-x * Real.cosh r)) (Ioi 0) := by
  simpa only [zero_mul, Real.cos_zero, mul_one] using moment_integrable j 0 hx

theorem moment_norm_decay (j : ℕ) (t : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ‖moment j t x‖ ≤ Real.exp (1-x) * moment j 0 1 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hg : IntegrableOn (fun r : ℝ => Real.exp (1-x) *
      (Real.cosh r ^ j * Real.exp (-1 * Real.cosh r))) (Ioi 0) :=
    (zero_moment_integrable j zero_lt_one).const_mul _
  calc
    ‖moment j t x‖ ≤ ∫ r in Ioi (0:ℝ),
        ‖Real.cosh r ^ j * Real.exp (-x * Real.cosh r) * Real.cos (t*r)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ r in Ioi (0:ℝ), Real.exp (1-x) *
        (Real.cosh r ^ j * Real.exp (-1 * Real.cosh r)) := by
      apply integral_mono (moment_integrable j t hx0).norm hg
      intro r
      have he : Real.exp (-x * Real.cosh r) ≤ Real.exp (1-x) * Real.exp (-1 * Real.cosh r) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr (Real.one_le_cosh r))]
      simp only [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (Real.cosh_pos r).le j), abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ Real.cosh r ^ j * Real.exp (-x * Real.cosh r) := by
          simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (t*r)) (by positivity :
            0 ≤ Real.cosh r ^ j * Real.exp (-x * Real.cosh r))
        _ ≤ Real.cosh r ^ j * (Real.exp (1-x) * Real.exp (-1 * Real.cosh r)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
        _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul]
      simp only [moment, zero_mul, Real.cos_zero, mul_one]

theorem moment_norm_bounded (j : ℕ) (t : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ‖moment j t x‖ ≤ moment j 0 1 := by
  have he : Real.exp (1-x) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  exact (moment_norm_decay j t hx).trans (by
    simpa using mul_le_mul_of_nonneg_right he (zero_moment_nonneg j 1))

/-- Polynomially weighted squares of the actual moments vanish at infinity. -/
theorem moment_product_tendsto (j k : ℕ) (t : ℝ) (n : ℕ) :
    Tendsto (fun x : ℝ => x^n * (moment j t x * moment k t x)) atTop (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => x^n * Real.exp (-2*x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n:ℝ) 2 (by norm_num)
  let C := Real.exp 2 * (moment j 0 1 * moment k 0 1)
  apply squeeze_zero_norm' _ (by simpa using he.const_mul C)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have h1 := moment_norm_decay j t hx
  have h2 := moment_norm_decay k t hx
  have hb := mul_le_mul h1 h2 (norm_nonneg _)
    (mul_nonneg (Real.exp_pos _).le (zero_moment_nonneg j 1))
  have heq : Real.exp (1-x) * Real.exp (1-x) = Real.exp 2 * Real.exp (-2*x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [← neg_mul]
  rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hx0]
  calc
    _ ≤ x^n * ((Real.exp (1-x) * moment j 0 1) *
        (Real.exp (1-x) * moment k 0 1)) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hx0 n)
    _ = C * (x^n * Real.exp (-2*x)) := by
      dsimp [C]
      calc
        _ = x^n * ((Real.exp (1-x) * Real.exp (1-x)) * (moment j 0 1 * moment k 0 1)) := by ring
        _ = _ := by rw [heq]; ring

#print axioms moment_norm_decay
#print axioms moment_product_tendsto

end MaassKBessel
