module

public import MaassKBesselMomentsV1

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace MaassKBessel

/-- Boundary term for the single integration-by-parts identity yielding
the modified Bessel equation. -/
noncomputable def boundary (t x r : ℝ) : ℝ :=
  Real.exp (-x * Real.cosh r) *
    (x * Real.sinh r * Real.cos (t*r) - t * Real.sin (t*r))

noncomputable def odeKernel (t x r : ℝ) : ℝ :=
  x^2 * (Real.cosh r ^ 2 * Real.exp (-x * Real.cosh r) * Real.cos (t*r)) -
  x * (Real.cosh r ^ 1 * Real.exp (-x * Real.cosh r) * Real.cos (t*r)) +
  (t^2-x^2) * (Real.cosh r ^ 0 * Real.exp (-x * Real.cosh r) * Real.cos (t*r))

theorem boundary_hasDerivAt (t x r : ℝ) :
    HasDerivAt (boundary t x) (-odeKernel t x r) r := by
  have hc := ((hasDerivAt_id r).const_mul t).cos
  have hs := ((hasDerivAt_id r).const_mul t).sin
  convert (((Real.hasDerivAt_cosh r).const_mul (-x)).exp.mul
    ((((Real.hasDerivAt_sinh r).const_mul x).mul hc).sub (hs.const_mul t))) using 1
  all_goals try funext y
  all_goals dsimp [boundary, odeKernel]
  all_goals simp only [pow_one, pow_zero, one_mul]
  all_goals rw [Real.cosh_sq]
  all_goals ring

theorem boundary_bound (t : ℝ) {x r : ℝ} (hx : 0 < x) (hr : 0 ≤ r) :
    ‖boundary t x r‖ ≤ (x * (1 / (x/2)) + |t|) * Real.exp (-(x/2)*r) := by
  have hsinh : |Real.sinh r| ≤ Real.cosh r := by
    rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr hr)]
    exact (Real.sinh_lt_cosh r).le
  have hbase : ‖boundary t x r‖ ≤
      x * (Real.cosh r * Real.exp (-x * Real.cosh r)) +
      |t| * Real.exp (-x * Real.cosh r) := by
    rw [boundary, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-x * Real.cosh r) *
          (‖x * Real.sinh r * Real.cos (t*r)‖ + ‖t * Real.sin (t*r)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le
      _ ≤ Real.exp (-x * Real.cosh r) * (x * Real.cosh r + |t|) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        simp only [norm_mul, Real.norm_eq_abs, abs_of_pos hx]
        apply add_le_add
        · calc
            x * |Real.sinh r| * |Real.cos (t*r)| ≤ x * |Real.sinh r| * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (mul_nonneg hx.le (abs_nonneg _))
            _ ≤ x * Real.cosh r := by
              rw [mul_one]
              exact mul_le_mul_of_nonneg_left hsinh hx.le
        · simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (t*r)) (abs_nonneg t)
      _ = _ := by ring
  have h1 : Real.cosh r * Real.exp (-x * Real.cosh r) ≤
      (1/(x/2)) * Real.exp (-(x/2)*r) := by
    simpa only [pow_one, zero_mul, Real.cos_zero, mul_one, Nat.factorial_one,
      Nat.cast_one, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos r),
      abs_of_pos (Real.exp_pos _)] using moment_majorant 1 0 hx hr
  have h0 : Real.exp (-x * Real.cosh r) ≤ Real.exp (-(x/2)*r) := by
    have h := kernel_majorant 0 hx hr
    simp only [zero_mul, Real.cos_zero, mul_one, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at h
    exact h.trans (Real.exp_le_exp.mpr (by nlinarith))
  calc
    _ ≤ x * (Real.cosh r * Real.exp (-x * Real.cosh r)) +
        |t| * Real.exp (-x * Real.cosh r) := hbase
    _ ≤ x * ((1/(x/2)) * Real.exp (-(x/2)*r)) + |t| * Real.exp (-(x/2)*r) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 hx.le) (mul_le_mul_of_nonneg_left h0 (abs_nonneg t))
    _ = _ := by ring

theorem boundary_tendsto (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (boundary t x) atTop (𝓝 0) := by
  have he : Tendsto (fun r : ℝ => Real.exp (-(x/2)*r)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (by linarith : -(x/2) < 0) tendsto_id)
  apply squeeze_zero_norm' _ (by simpa using he.const_mul (x * (1/(x/2)) + |t|))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  simpa using boundary_bound t hx hr

theorem odeKernel_integrable (t : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (odeKernel t x) (Ioi 0) := by
  have h := (((moment_integrable 2 t hx).const_mul (x^2)).sub
    ((moment_integrable 1 t hx).const_mul x)).add ((moment_integrable 0 t hx).const_mul (t^2-x^2))
  change Integrable (fun r => odeKernel t x r) (volume.restrict (Ioi 0))
  convert h using 1
  ext r
  simp [odeKernel]

/-- The actual integral moments satisfy the Bessel differential equation. -/
theorem moment_ode (t : ℝ) {x : ℝ} (hx : 0 < x) :
    x^2 * moment 2 t x - x * moment 1 t x + (t^2-x^2) * K t x = 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r (_ : r ∈ Ici (0 : ℝ)) => boundary_hasDerivAt t x r)
    (odeKernel_integrable t hx).neg (boundary_tendsto t hx)
  have hb : boundary t x 0 = 0 := by simp [boundary]
  rw [integral_neg, hb, sub_zero, neg_eq_zero] at h
  have h2 := (moment_integrable 2 t hx).const_mul (x^2)
  have h1 := (moment_integrable 1 t hx).const_mul x
  have h0 := (moment_integrable 0 t hx).const_mul (t^2-x^2)
  change (∫ r in Ioi (0 : ℝ), odeKernel t x r) = 0 at h
  have h2' : IntegrableOn (fun r : ℝ => x^2 *
      (Real.cosh r ^ 2 * Real.exp (-x * Real.cosh r) * Real.cos (t*r))) (Ioi 0) := h2
  have h1' : IntegrableOn (fun r : ℝ => x *
      (Real.cosh r ^ 1 * Real.exp (-x * Real.cosh r) * Real.cos (t*r))) (Ioi 0) := h1
  have h0' : IntegrableOn (fun r : ℝ => (t^2-x^2) *
      (Real.cosh r ^ 0 * Real.exp (-x * Real.cosh r) * Real.cos (t*r))) (Ioi 0) := h0
  dsimp only [odeKernel] at h
  have h21 : IntegrableOn (fun r : ℝ =>
      x^2 * (Real.cosh r ^ 2 * Real.exp (-x * Real.cosh r) * Real.cos (t*r)) -
      x * (Real.cosh r ^ 1 * Real.exp (-x * Real.cosh r) * Real.cos (t*r)))
      (Ioi 0) := h2'.sub h1'
  rw [integral_add h21 h0', integral_sub h2' h1',
    integral_const_mul, integral_const_mul, integral_const_mul] at h
  simpa only [moment, K, pow_zero, one_mul] using h

theorem deriv_K (t : ℝ) {x : ℝ} (hx : 0 < x) : deriv (K t) x = -moment 1 t x :=
  (K_hasDerivAt t hx).deriv

theorem deriv_K_hasDerivAt (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv (K t)) (moment 2 t x) x := by
  have h : HasDerivAt (fun y => -moment 1 t y) (moment 2 t x) x := by
    convert (moment_hasDerivAt 1 t hx).neg using 1
    simp only [neg_neg, Nat.reduceAdd]
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact deriv_K t hy

/-- The modified Bessel equation for the actual integral and its actual derivatives. -/
theorem bessel_ode (t : ℝ) {x : ℝ} (hx : 0 < x) :
    x^2 * deriv (deriv (K t)) x + x * deriv (K t) x + (t^2-x^2) * K t x = 0 := by
  rw [(deriv_K_hasDerivAt t hx).deriv, deriv_K t hx]
  nlinarith [moment_ode t hx]

#print axioms moment_ode
#print axioms bessel_ode

end MaassKBessel
