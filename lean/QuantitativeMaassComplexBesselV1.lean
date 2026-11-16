module

public import QuantitativeMaassEulerDecayV1
public import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Actual Bessel integrand with its argument in the complex right half-plane. -/
def principalComplexKernel (j : ℕ) (r : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.cosh u)^j:ℂ)*Complex.exp (-z*(Real.cosh u:ℂ))*(Real.cos (r*u):ℂ)

def principalComplexMoment (j : ℕ) (r : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0:ℝ),principalComplexKernel j r z u

theorem principalComplexKernel_norm_bound (j : ℕ) (r : ℝ) (z : ℂ) (u : ℝ) :
    ‖principalComplexKernel j r z u‖≤Real.cosh u^j*Real.exp (-z.re*Real.cosh u) := by
  unfold principalComplexKernel
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos u),Complex.norm_exp,Complex.mul_re,Complex.neg_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (r*u))
    (show 0≤Real.cosh u^j*Real.exp (-z.re*Real.cosh u) by positivity)

theorem principalComplexKernel_integrable (j : ℕ) (r : ℝ) (z : ℂ) (hz : 0<z.re) :
    IntegrableOn (principalComplexKernel j r z) (Ioi 0) := by
  apply (MaassKBessel.zero_moment_integrable j hz).mono'
  · exact (by unfold principalComplexKernel; fun_prop : Continuous (principalComplexKernel j r z)).aestronglyMeasurable
  · exact Eventually.of_forall (fun u => principalComplexKernel_norm_bound j r z u)

theorem principalComplexKernel_hasDerivAt (j : ℕ) (r u : ℝ) (z : ℂ) :
    HasDerivAt (fun w => principalComplexKernel j r w u) (-principalComplexKernel (j+1) r z u) z := by
  have hh := (((((hasDerivAt_id z).neg).mul_const (Real.cosh u:ℂ)).cexp.const_mul
    ((Real.cosh u)^j:ℂ)).mul_const (Real.cos (r*u):ℂ))
  convert hh using 1
  · rfl
  · unfold principalComplexKernel
    rw [pow_succ]
    simp only [Pi.neg_apply,id_eq,neg_mul,one_mul]
    ring

/-- Holomorphic differentiation of the actual integral, with a uniform
integrable majorant on a neighborhood in the right half-plane. -/
theorem principalComplexMoment_hasDerivAt (j : ℕ) (r : ℝ) (z : ℂ) (hz : 0<z.re) :
    HasDerivAt (principalComplexMoment j r) (-principalComplexMoment (j+1) r z) z := by
  let μ := volume.restrict (Ioi (0:ℝ))
  let B := fun u : ℝ => Real.cosh u^(j+1)*Real.exp (-(z.re/2)*Real.cosh u)
  have hb : Integrable B μ := MaassKBessel.zero_moment_integrable (j+1) (by positivity)
  have hU : {w : ℂ | z.re/2<w.re}∈𝓝 z :=
    Complex.continuous_re.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith : z.re/2<z.re))
  have hm : ∀ᶠ w in 𝓝 z,AEStronglyMeasurable (principalComplexKernel j r w) μ :=
    Eventually.of_forall (fun w => (by unfold principalComplexKernel; fun_prop : Continuous (principalComplexKernel j r w)).aestronglyMeasurable)
  have hm' : AEStronglyMeasurable (fun u => -principalComplexKernel (j+1) r z u) μ :=
    (by unfold principalComplexKernel; fun_prop : Continuous (fun u => -principalComplexKernel (j+1) r z u)).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂μ,∀ w∈{w : ℂ | z.re/2<w.re},‖-principalComplexKernel (j+1) r w u‖≤B u := by
    apply Eventually.of_forall
    intro u w hw
    rw [norm_neg]
    apply (principalComplexKernel_norm_bound (j+1) r w u).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hw.le) (Real.cosh_pos u).le
  have hd : ∀ᵐ u ∂μ,∀ w∈{w : ℂ | z.re/2<w.re},
      HasDerivAt (fun w => principalComplexKernel j r w u) (-principalComplexKernel (j+1) r w u) w :=
    Eventually.of_forall (fun u w _ => principalComplexKernel_hasDerivAt j r u w)
  change HasDerivAt (fun w => ∫ u in Ioi (0:ℝ),principalComplexKernel j r w u)
    (-(∫ u in Ioi (0:ℝ),principalComplexKernel (j+1) r z u)) z
  rw [←integral_neg]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU hm
    (principalComplexKernel_integrable j r z hz) hm' hbound hb hd).2

theorem principalComplexMoment_analytic (j : ℕ) (r : ℝ) :
    AnalyticOnNhd ℂ (principalComplexMoment j r) {z : ℂ | 0<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  exact (principalComplexMoment_hasDerivAt j r z hz).differentiableAt.differentiableWithinAt

/-- The complex extension restricts to the previously checked actual real Bessel moment. -/
theorem principalComplexMoment_ofReal (j : ℕ) (r x : ℝ) :
    principalComplexMoment j r (x:ℂ)=(MaassKBessel.moment j r x:ℂ) := by
  have he (u : ℝ) : principalComplexKernel j r (x:ℂ) u=
      ((Real.cosh u^j*Real.exp (-x*Real.cosh u)*Real.cos (r*u):ℝ):ℂ) := by
    simp only [principalComplexKernel,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_exp,Complex.ofReal_neg]
  unfold principalComplexMoment MaassKBessel.moment
  simp_rw [he]
  exact integral_complex_ofReal

#print axioms principalComplexKernel_norm_bound
#print axioms principalComplexKernel_integrable
#print axioms principalComplexKernel_hasDerivAt
#print axioms principalComplexMoment_hasDerivAt
#print axioms principalComplexMoment_analytic
#print axioms principalComplexMoment_ofReal

end QuantitativeMaass
