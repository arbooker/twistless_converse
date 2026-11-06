module

public import MaassExceptionalIntegralV1

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace MaassExceptional

/-- The plus sign in this boundary term is essential for real Bessel order. -/
noncomputable def boundary (τ x r : ℝ) : ℝ :=
  Real.exp (-x * Real.cosh r) *
    (x * Real.sinh r * Real.cosh (τ*r) + τ * Real.sinh (τ*r))

noncomputable def odeKernel (τ x r : ℝ) : ℝ :=
  x^2 * (Real.cosh r ^ 2 * Real.exp (-x * Real.cosh r) * Real.cosh (τ*r)) -
  x * (Real.cosh r ^ 1 * Real.exp (-x * Real.cosh r) * Real.cosh (τ*r)) -
  (τ^2+x^2) * (Real.cosh r ^ 0 * Real.exp (-x * Real.cosh r) * Real.cosh (τ*r))

theorem boundary_hasDerivAt (τ x r : ℝ) :
    HasDerivAt (boundary τ x) (-odeKernel τ x r) r := by
  have hc := ((hasDerivAt_id r).const_mul τ).cosh
  have hs := ((hasDerivAt_id r).const_mul τ).sinh
  convert (((Real.hasDerivAt_cosh r).const_mul (-x)).exp.mul
    ((((Real.hasDerivAt_sinh r).const_mul x).mul hc).add (hs.const_mul τ))) using 1
  all_goals try funext y
  all_goals dsimp [boundary, odeKernel]
  all_goals simp only [pow_one, pow_zero, one_mul]
  all_goals rw [Real.cosh_sq]
  all_goals ring

theorem abs_sinh_le_cosh (r : ℝ) : |Real.sinh r| ≤ Real.cosh r := by
  apply abs_le.mpr
  constructor
  · have h := Real.sinh_lt_cosh (-r)
    rw [Real.sinh_neg, Real.cosh_neg] at h
    linarith
  · exact (Real.sinh_lt_cosh r).le

theorem boundary_bound {τ x r : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) (hr : 0 ≤ r) :
    ‖boundary τ x r‖ ≤
      (x * (2 / (x/2)^2) + |τ| * (1/(x/2))) * Real.exp (-(x/2)*r) := by
  have hb : ‖boundary τ x r‖ ≤
      x * (Real.cosh r ^ 2 * Real.exp (-x * Real.cosh r)) +
      |τ| * (Real.cosh r * Real.exp (-x * Real.cosh r)) := by
    rw [boundary, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-x * Real.cosh r) *
          (‖x * Real.sinh r * Real.cosh (τ*r)‖ + ‖τ * Real.sinh (τ*r)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
      _ ≤ Real.exp (-x * Real.cosh r) * (x * Real.cosh r ^ 2 + |τ| * Real.cosh r) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        simp only [norm_mul, Real.norm_eq_abs, abs_of_pos hx, abs_of_pos (Real.cosh_pos _)]
        apply add_le_add
        · calc
            x * |Real.sinh r| * Real.cosh (τ*r) ≤ x * Real.cosh r * Real.cosh r :=
              mul_le_mul (mul_le_mul_of_nonneg_left (abs_sinh_le_cosh r) hx.le)
                (cosh_mul_le hτ hr) (Real.cosh_pos _).le (by positivity)
            _ = _ := by ring
        · exact mul_le_mul_of_nonneg_left
            ((abs_sinh_le_cosh (τ*r)).trans (cosh_mul_le hτ hr)) (abs_nonneg _)
      _ = _ := by ring
  have h2 : Real.cosh r ^ 2 * Real.exp (-x * Real.cosh r) ≤
      (2/(x/2)^2) * Real.exp (-(x/2)*r) := by
    simpa only [zero_mul, Real.cos_zero, mul_one, Nat.factorial_two, Nat.cast_ofNat,
      Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ Real.cosh r ^ 2 * Real.exp (-x * Real.cosh r))] using
      MaassKBessel.moment_majorant 2 0 hx hr
  have h1 : Real.cosh r * Real.exp (-x * Real.cosh r) ≤
      (1/(x/2)) * Real.exp (-(x/2)*r) := by
    simpa only [pow_one, zero_mul, Real.cos_zero, mul_one, Nat.factorial_one,
      Nat.cast_one, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos r),
      abs_of_pos (Real.exp_pos _)] using MaassKBessel.moment_majorant 1 0 hx hr
  calc
    _ ≤ x * (Real.cosh r ^ 2 * Real.exp (-x * Real.cosh r)) +
        |τ| * (Real.cosh r * Real.exp (-x * Real.cosh r)) := hb
    _ ≤ x * ((2/(x/2)^2) * Real.exp (-(x/2)*r)) +
        |τ| * ((1/(x/2)) * Real.exp (-(x/2)*r)) :=
      add_le_add (mul_le_mul_of_nonneg_left h2 hx.le) (mul_le_mul_of_nonneg_left h1 (abs_nonneg τ))
    _ = _ := by ring

theorem boundary_tendsto {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    Tendsto (boundary τ x) atTop (𝓝 0) := by
  have he : Tendsto (fun r : ℝ => Real.exp (-(x/2)*r)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (by linarith : -(x/2) < 0) tendsto_id)
  apply squeeze_zero_norm' _
    (by simpa using he.const_mul (x * (2/(x/2)^2) + |τ| * (1/(x/2))))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  simpa using boundary_bound hτ hx hr

theorem odeKernel_integrable {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    IntegrableOn (odeKernel τ x) (Ioi 0) := by
  have h := (((moment_integrable 2 hτ hx).const_mul (x^2)).sub
    ((moment_integrable 1 hτ hx).const_mul x)).sub ((moment_integrable 0 hτ hx).const_mul (τ^2+x^2))
  change Integrable (fun r => odeKernel τ x r) (volume.restrict (Ioi 0))
  convert h using 1
  ext r
  simp [odeKernel]

theorem moment_ode {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    x^2 * moment 2 τ x - x * moment 1 τ x - (τ^2+x^2) * K τ x = 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r (_ : r ∈ Ici (0 : ℝ)) => boundary_hasDerivAt τ x r)
    (odeKernel_integrable hτ hx).neg (boundary_tendsto hτ hx)
  have hb : boundary τ x 0 = 0 := by simp [boundary]
  rw [integral_neg, hb, sub_zero, neg_eq_zero] at h
  have h2 : IntegrableOn (fun r : ℝ => x^2 *
      (Real.cosh r ^ 2 * Real.exp (-x * Real.cosh r) * Real.cosh (τ*r))) (Ioi 0) :=
    (moment_integrable 2 hτ hx).const_mul _
  have h1 : IntegrableOn (fun r : ℝ => x *
      (Real.cosh r ^ 1 * Real.exp (-x * Real.cosh r) * Real.cosh (τ*r))) (Ioi 0) :=
    (moment_integrable 1 hτ hx).const_mul _
  have h0 : IntegrableOn (fun r : ℝ => (τ^2+x^2) *
      (Real.cosh r ^ 0 * Real.exp (-x * Real.cosh r) * Real.cosh (τ*r))) (Ioi 0) :=
    (moment_integrable 0 hτ hx).const_mul _
  have h21 : IntegrableOn (fun r : ℝ =>
      x^2 * (Real.cosh r ^ 2 * Real.exp (-x * Real.cosh r) * Real.cosh (τ*r)) -
      x * (Real.cosh r ^ 1 * Real.exp (-x * Real.cosh r) * Real.cosh (τ*r)))
      (Ioi 0) := h2.sub h1
  change (∫ r in Ioi (0 : ℝ), odeKernel τ x r) = 0 at h
  dsimp only [odeKernel] at h
  rw [integral_sub h21 h0, integral_sub h2 h1,
    integral_const_mul, integral_const_mul, integral_const_mul] at h
  simpa only [moment, K] using h

theorem deriv_K {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    deriv (K τ) x = -moment 1 τ x := (K_hasDerivAt hτ hx).deriv

theorem deriv_K_hasDerivAt {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    HasDerivAt (deriv (K τ)) (moment 2 τ x) x := by
  have h : HasDerivAt (fun y => -moment 1 τ y) (moment 2 τ x) x := by
    convert (moment_hasDerivAt 1 hτ hx).neg using 1
    simp only [neg_neg, Nat.reduceAdd]
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact deriv_K hτ hy

/-- Actual real-order modified Bessel equation; no ODE assumption. -/
theorem bessel_ode {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    x^2 * deriv (deriv (K τ)) x + x * deriv (K τ) x - (τ^2+x^2) * K τ x = 0 := by
  rw [(deriv_K_hasDerivAt hτ hx).deriv, deriv_K hτ hx]
  nlinarith [moment_ode hτ hx]

#print axioms moment_ode
#print axioms bessel_ode

end MaassExceptional
