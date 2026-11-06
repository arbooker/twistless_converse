module

public import MaassKBesselIntegralV1
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace MaassKBessel

/-- A polynomial factor can be absorbed by half of the exponential decay. -/
theorem pow_mul_exp_bound (j : ℕ) {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    u ^ j * Real.exp (-c * u) ≤ (j.factorial : ℝ) / c ^ j := by
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
  have hh := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (c*u) (mul_nonneg hc.le hu) j)
  have hb : (c*u)^j * Real.exp (-c*u) ≤ (j.factorial : ℝ) := by
    calc
      (c*u)^j * Real.exp (-c*u) ≤
          (Real.exp (c*u) * (j.factorial : ℝ)) * Real.exp (-c*u) :=
        mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
      _ = (j.factorial : ℝ) := by
        rw [mul_right_comm, ← Real.exp_add]
        ring_nf
        simp
  calc
    u^j * Real.exp (-c*u) = ((c*u)^j * Real.exp (-c*u)) / c^j := by
      rw [mul_pow]
      field_simp
    _ ≤ (j.factorial : ℝ) / c^j := div_le_div_of_nonneg_right hb (pow_pos hc j).le

theorem moment_majorant (j : ℕ) (t : ℝ) {x r : ℝ} (hx : 0 < x) (hr : 0 ≤ r) :
    ‖Real.cosh r ^ j * Real.exp (-x * Real.cosh r) * Real.cos (t*r)‖ ≤
      ((j.factorial : ℝ) / (x/2)^j) * Real.exp (-(x/2)*r) := by
  have hc : 0 < x/2 := by linarith
  have he : Real.exp (-x * Real.cosh r) =
      Real.exp (-(x/2) * Real.cosh r) * Real.exp (-(x/2) * Real.cosh r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hC : 0 ≤ (j.factorial : ℝ) / (x/2)^j := by positivity
  rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.cosh_pos r).le j),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
  calc
    _ ≤ Real.cosh r ^ j * Real.exp (-x * Real.cosh r) := by
      simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (t*r))
        (mul_nonneg (pow_nonneg (Real.cosh_pos r).le j) (Real.exp_pos _).le)
    _ = (Real.cosh r ^ j * Real.exp (-(x/2) * Real.cosh r)) *
        Real.exp (-(x/2) * Real.cosh r) := by rw [he]; ring
    _ ≤ ((j.factorial : ℝ) / (x/2)^j) * Real.exp (-(x/2) * Real.cosh r) :=
      mul_le_mul_of_nonneg_right (pow_mul_exp_bound j hc (Real.cosh_pos r).le) (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left (self_le_cosh_of_nonneg hr) (by linarith))) hC

theorem moment_integrable (j : ℕ) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun r : ℝ => Real.cosh r ^ j * Real.exp (-x * Real.cosh r) *
      Real.cos (t*r)) (Ioi 0) := by
  have hg := (integrableOn_exp_mul_Ioi (a := -(x/2)) (by linarith) 0).const_mul
    ((j.factorial : ℝ) / (x/2)^j)
  apply hg.mono'
  · exact (by fun_prop : Continuous (fun r : ℝ => Real.cosh r ^ j *
      Real.exp (-x * Real.cosh r) * Real.cos (t*r))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact moment_majorant j t hx hr.le

/-- Actual integral moments, used to differentiate `K` in its argument. -/
noncomputable def moment (j : ℕ) (t x : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), Real.cosh r ^ j * Real.exp (-x * Real.cosh r) * Real.cos (t*r)

theorem moment_zero (t x : ℝ) : moment 0 t x = K t x := by simp [moment, K]

theorem moment_norm_antitone (j : ℕ) (t r : ℝ) {x y : ℝ} (hxy : x ≤ y) :
    ‖Real.cosh r ^ j * Real.exp (-y * Real.cosh r) * Real.cos (t*r)‖ ≤
    ‖Real.cosh r ^ j * Real.exp (-x * Real.cosh r) * Real.cos (t*r)‖ := by
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hxy) (Real.cosh_pos r).le)

theorem moment_kernel_hasDerivAt (j : ℕ) (t x r : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cosh r ^ j * Real.exp (-y * Real.cosh r) * Real.cos (t*r))
      (-(Real.cosh r ^ (j+1) * Real.exp (-x * Real.cosh r) * Real.cos (t*r))) x := by
  convert (((((hasDerivAt_id x).neg).mul_const (Real.cosh r)).exp.const_mul
    (Real.cosh r ^ j)).mul_const (Real.cos (t*r))) using 1
  all_goals try funext y
  all_goals dsimp
  all_goals simp only [pow_succ]
  all_goals ring

/-- Differentiation under the actual integral, justified by a local
integrable exponential majorant for every moment. -/
theorem moment_hasDerivAt (j : ℕ) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (moment j t) (-moment (j+1) t x) x := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℝ := fun y r => Real.cosh r ^ j * Real.exp (-y * Real.cosh r) * Real.cos (t*r)
  let F' : ℝ → ℝ → ℝ := fun y r =>
    -(Real.cosh r ^ (j+1) * Real.exp (-y * Real.cosh r) * Real.cos (t*r))
  let B : ℝ → ℝ := fun r => (((j+1).factorial : ℝ) / (x/4)^(j+1)) * Real.exp (-(x/4)*r)
  have hb : Integrable B μ := by
    exact (integrableOn_exp_mul_Ioi (a := -(x/4)) (by linarith) 0).const_mul _
  have hbound : ∀ᵐ r ∂μ, ∀ y ∈ Ioi (x/2), ‖F' y r‖ ≤ B r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    intro y hy
    dsimp [F', B]
    rw [abs_neg]
    have h := (moment_norm_antitone (j+1) t r hy.le).trans
      (moment_majorant (j+1) t (by linarith : 0 < x/2) hr.le)
    convert h using 1
    all_goals congr 2
    all_goals ring
  have hm : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) μ :=
    Filter.Eventually.of_forall fun y => (by fun_prop : Continuous (F y)).aestronglyMeasurable
  have hm' : AEStronglyMeasurable (F' x) μ :=
    (by fun_prop : Continuous (F' x)).aestronglyMeasurable
  have hd : ∀ᵐ r ∂μ, ∀ y ∈ Ioi (x/2), HasDerivAt (F · r) (F' y r) y := by
    exact Filter.Eventually.of_forall fun r y _ => moment_kernel_hasDerivAt j t y r
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioi_mem_nhds (by linarith : x/2 < x)) hm (moment_integrable j t hx) hm' hbound hb hd).2
  change HasDerivAt (fun y => moment j t y) (-moment (j+1) t x) x
  simpa [F, F', μ, moment, integral_neg] using h

theorem K_hasDerivAt (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (K t) (-moment 1 t x) x := by
  have heq : moment 0 t = K t := funext (moment_zero t)
  simpa only [heq, Nat.zero_add] using moment_hasDerivAt 0 t hx

#print axioms moment_integrable
#print axioms moment_hasDerivAt
#print axioms K_hasDerivAt

end MaassKBessel
