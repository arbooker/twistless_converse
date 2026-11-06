module

public import MaassKBesselMomentsV1

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace MaassExceptional

/-- The real-order integral, distinct from the imaginary-order cosine kernel.
For the Maass exceptional spectrum use `|τ| < 1/2`. The elementary results
in this file hold on the larger closed range `|τ| ≤ 1`. -/
noncomputable def moment (j : ℕ) (τ x : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), Real.cosh r ^ j * Real.exp (-x * Real.cosh r) * Real.cosh (τ*r)

noncomputable def K (τ x : ℝ) : ℝ := moment 0 τ x

theorem cosh_mul_le {τ r : ℝ} (hτ : |τ| ≤ 1) (hr : 0 ≤ r) :
    Real.cosh (τ*r) ≤ Real.cosh r := by
  apply Real.cosh_le_cosh.mpr
  rw [abs_mul, abs_of_nonneg hr]
  simpa using mul_le_mul_of_nonneg_right hτ hr

theorem moment_majorant (j : ℕ) {τ x r : ℝ}
    (hτ : |τ| ≤ 1) (hx : 0 < x) (hr : 0 ≤ r) :
    ‖Real.cosh r ^ j * Real.exp (-x * Real.cosh r) * Real.cosh (τ*r)‖ ≤
      (((j+1).factorial : ℝ) / (x/2)^(j+1)) * Real.exp (-(x/2)*r) := by
  have hb := MaassKBessel.moment_majorant (j+1) 0 hx hr
  simp only [zero_mul, Real.cos_zero, mul_one,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (pow_nonneg (Real.cosh_pos r).le (j+1)) (Real.exp_pos _).le)] at hb
  rw [Real.norm_eq_abs, abs_of_pos (by positivity :
    0 < Real.cosh r ^ j * Real.exp (-x * Real.cosh r) * Real.cosh (τ*r))]
  calc
    _ ≤ Real.cosh r ^ j * Real.exp (-x * Real.cosh r) * Real.cosh r :=
      mul_le_mul_of_nonneg_left (cosh_mul_le hτ hr) (by positivity)
    _ = Real.cosh r ^ (j+1) * Real.exp (-x * Real.cosh r) := by rw [pow_succ]; ring
    _ ≤ _ := hb

theorem moment_integrable (j : ℕ) {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    IntegrableOn (fun r : ℝ => Real.cosh r ^ j * Real.exp (-x * Real.cosh r) *
      Real.cosh (τ*r)) (Ioi 0) := by
  have hg := (integrableOn_exp_mul_Ioi (a := -(x/2)) (by linarith) 0).const_mul
    (((j+1).factorial : ℝ) / (x/2)^(j+1))
  apply hg.mono'
  · exact (by fun_prop : Continuous (fun r : ℝ => Real.cosh r ^ j *
      Real.exp (-x * Real.cosh r) * Real.cosh (τ*r))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact moment_majorant j hτ hx hr.le

theorem K_neg_order (τ x : ℝ) : K (-τ) x = K τ x := by
  simp [K, moment, neg_mul]

theorem K_zero_le {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    MaassKBessel.K 0 x ≤ K τ x := by
  simp only [MaassKBessel.K, zero_mul, Real.cos_zero, mul_one, K, moment, pow_zero, one_mul]
  apply integral_mono (MaassKBessel.kernel_zero_integrable hx)
    (by simpa only [IntegrableOn, pow_zero, one_mul] using moment_integrable 0 hτ hx)
  intro r
  simpa using mul_le_mul_of_nonneg_left (Real.one_le_cosh (τ*r)) (Real.exp_pos _).le

theorem K_pos {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) : 0 < K τ x :=
  (MaassKBessel.K_zero_pos hx).trans_le (K_zero_le hτ hx)

theorem moment_norm_antitone (j : ℕ) (τ r : ℝ) {x y : ℝ} (hxy : x ≤ y) :
    ‖Real.cosh r ^ j * Real.exp (-y * Real.cosh r) * Real.cosh (τ*r)‖ ≤
    ‖Real.cosh r ^ j * Real.exp (-x * Real.cosh r) * Real.cosh (τ*r)‖ := by
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hxy) (Real.cosh_pos r).le)

theorem moment_kernel_hasDerivAt (j : ℕ) (τ x r : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cosh r ^ j * Real.exp (-y * Real.cosh r) * Real.cosh (τ*r))
      (-(Real.cosh r ^ (j+1) * Real.exp (-x * Real.cosh r) * Real.cosh (τ*r))) x := by
  convert (((((hasDerivAt_id x).neg).mul_const (Real.cosh r)).exp.const_mul
    (Real.cosh r ^ j)).mul_const (Real.cosh (τ*r))) using 1
  all_goals try funext y
  all_goals dsimp
  all_goals simp only [pow_succ]
  all_goals ring

/-- Differentiation of the actual exceptional moments. The derivative's
local majorant has index j+2, including the extra hyperbolic factor. -/
theorem moment_hasDerivAt (j : ℕ) {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    HasDerivAt (moment j τ) (-moment (j+1) τ x) x := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℝ := fun y r => Real.cosh r ^ j * Real.exp (-y * Real.cosh r) * Real.cosh (τ*r)
  let F' : ℝ → ℝ → ℝ := fun y r =>
    -(Real.cosh r ^ (j+1) * Real.exp (-y * Real.cosh r) * Real.cosh (τ*r))
  let B : ℝ → ℝ := fun r => (((j+2).factorial : ℝ) / (x/4)^(j+2)) * Real.exp (-(x/4)*r)
  have hb : Integrable B μ := by
    exact (integrableOn_exp_mul_Ioi (a := -(x/4)) (by linarith) 0).const_mul _
  have hbound : ∀ᵐ r ∂μ, ∀ y ∈ Ioi (x/2), ‖F' y r‖ ≤ B r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    intro y hy
    dsimp [F', B]
    rw [abs_neg]
    have h := (moment_norm_antitone (j+1) τ r hy.le).trans
      (moment_majorant (j+1) hτ (by linarith : 0 < x/2) hr.le)
    convert h using 1
    all_goals congr 2
    all_goals ring
  have hm : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) μ :=
    Filter.Eventually.of_forall fun y => (by fun_prop : Continuous (F y)).aestronglyMeasurable
  have hm' : AEStronglyMeasurable (F' x) μ :=
    (by fun_prop : Continuous (F' x)).aestronglyMeasurable
  have hd : ∀ᵐ r ∂μ, ∀ y ∈ Ioi (x/2), HasDerivAt (F · r) (F' y r) y := by
    exact Filter.Eventually.of_forall fun r y _ => moment_kernel_hasDerivAt j τ y r
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioi_mem_nhds (by linarith : x/2 < x)) hm (moment_integrable j hτ hx) hm' hbound hb hd).2
  change HasDerivAt (fun y => moment j τ y) (-moment (j+1) τ x) x
  simpa [F, F', μ, moment, integral_neg] using h

theorem K_hasDerivAt {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    HasDerivAt (K τ) (-moment 1 τ x) x :=
  moment_hasDerivAt 0 hτ hx

#print axioms moment_integrable
#print axioms K_pos
#print axioms moment_hasDerivAt
#print axioms K_hasDerivAt

end MaassExceptional
