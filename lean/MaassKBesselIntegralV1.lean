module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace MaassKBessel

/-- The actual real integral defining the modified Bessel function of
imaginary order. Analytic assertions below require `0 < x`. -/
noncomputable def K (t x : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), Real.exp (-x * Real.cosh r) * Real.cos (t * r)

theorem self_le_cosh_of_nonneg {r : ℝ} (hr : 0 ≤ r) : r ≤ Real.cosh r := by
  have hs := Real.self_le_sinh_iff.mpr hr
  have he := Real.exp_pos (-r)
  have hi := Real.cosh_sub_sinh (x := r)
  linarith

theorem kernel_majorant (t : ℝ) {x r : ℝ} (hx : 0 < x) (hr : 0 ≤ r) :
    ‖Real.exp (-x * Real.cosh r) * Real.cos (t * r)‖ ≤ Real.exp (-x * r) := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
  calc
    Real.exp (-x * Real.cosh r) * |Real.cos (t * r)| ≤
        Real.exp (-x * Real.cosh r) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ ≤ Real.exp (-x * r) := by
      rw [mul_one]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
        (self_le_cosh_of_nonneg hr) (neg_nonpos.mpr hx.le))

theorem kernel_integrable (t : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun r : ℝ => Real.exp (-x * Real.cosh r) * Real.cos (t * r))
      (Ioi 0) := by
  have hg := integrableOn_exp_mul_Ioi (a := -x) (neg_neg_of_pos hx) 0
  apply hg.mono'
  · exact (by fun_prop : Continuous
      (fun r : ℝ => Real.exp (-x * Real.cosh r) * Real.cos (t * r))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact kernel_majorant t hx hr.le

theorem K_neg_order (t x : ℝ) : K (-t) x = K t x := by
  simp [K, neg_mul]

theorem kernel_zero_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun r : ℝ => Real.exp (-x * Real.cosh r)) (Ioi 0) := by
  simpa using kernel_integrable 0 hx

theorem abs_K_le_K_zero (t : ℝ) {x : ℝ} (hx : 0 < x) : |K t x| ≤ K 0 x := by
  simp only [K, zero_mul, Real.cos_zero, mul_one]
  refine abs_integral_le_integral_abs.trans (integral_mono
    (kernel_integrable t hx).abs (kernel_zero_integrable hx) ?_)
  intro r
  dsimp only
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (t * r))
    (Real.exp_pos (-x * Real.cosh r)).le

theorem K_zero_pos {x : ℝ} (hx : 0 < x) : 0 < K 0 x := by
  simp only [K, zero_mul, Real.cos_zero, mul_one]
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun r => (Real.exp_pos (-x * Real.cosh r)).le))
    (kernel_zero_integrable hx)).mpr
  have hs : Function.support (fun r : ℝ => Real.exp (-(x * Real.cosh r))) = univ := by
    ext r
    simp [Function.mem_support, Real.exp_ne_zero]
  simp only [neg_mul]
  rw [hs, univ_inter]
  simp

#print axioms kernel_integrable
#print axioms abs_K_le_K_zero
#print axioms K_zero_pos

end MaassKBessel
