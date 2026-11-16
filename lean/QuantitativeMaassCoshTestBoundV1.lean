module

public import QuantitativeMaassPositiveTimeTestV1
public import QuantitativeMaassAbelOperatorBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem coshTestLift_deriv (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (q : ℝ) (hq : 1<q) :
    deriv (coshTestLift ψ) q=((Real.sqrt (q^2-1))⁻¹:ℂ)*deriv ψ (Real.arcosh q) := by
  have he : coshTestLift ψ=ᶠ[𝓝 q] (fun v => ψ (Real.arcosh v)) := by
    filter_upwards [Ioi_mem_nhds hq] with v hv
    exact ite_eq_left hv
  rw [he.deriv_eq]
  have h := ((hψ.differentiable (by simp) (Real.arcosh q)).hasDerivAt).scomp q
    (Real.hasDerivAt_arcosh hq)
  simpa only [Function.comp_def,Complex.real_smul,Complex.ofReal_inv] using h.deriv

/-- Positive separation of the time support from0 controls the derivative
of its smooth q-lift by 1/sinh(delta), including the extension region. -/
theorem coshTestLift_deriv_bound (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (δ R C : ℝ) (hδ : 0<δ) (hs : Function.support ψ⊆Icc δ R)
    (hb : ∀ t,‖deriv ψ t‖≤C) (q : ℝ) : ‖deriv (coshTestLift ψ) q‖≤C/Real.sinh δ := by
  have hC : 0≤C := (norm_nonneg (deriv ψ 0)).trans (hb 0)
  have hsδ : 0<Real.sinh δ := Real.sinh_pos_iff.mpr hδ
  by_cases hq : q<Real.cosh δ
  · have he : coshTestLift ψ=ᶠ[𝓝 q] (fun _ => (0:ℂ)) := by
      filter_upwards [Iio_mem_nhds hq] with v hv
      exact coshTestLift_zero_below ψ δ R hδ hs hv
    have hd : deriv (coshTestLift ψ) q=0 := by simpa using he.deriv_eq
    rw [hd,norm_zero]
    exact div_nonneg hC hsδ.le
  · have hq1 : 1<q := lt_of_lt_of_le (Real.one_lt_cosh.mpr (ne_of_gt hδ)) (le_of_not_gt hq)
    have ht : δ≤Real.arcosh q := by
      have hcos : Real.cosh δ≤Real.cosh (Real.arcosh q) := by
        rw [Real.cosh_arcosh hq1.le]
        exact le_of_not_gt hq
      have h := Real.cosh_le_cosh.mp hcos
      simpa only [abs_of_pos hδ,abs_of_nonneg (Real.arcosh_nonneg hq1.le)] using h
    have hl : Real.sinh δ≤Real.sqrt (q^2-1) := by
      rw [← Real.sinh_arcosh hq1.le]
      exact Real.sinh_le_sinh.mpr ht
    have hi : (Real.sqrt (q^2-1))⁻¹≤(Real.sinh δ)⁻¹ := inv_anti₀ hsδ hl
    rw [coshTestLift_deriv ψ hψ q hq1,norm_mul]
    have hn : ‖((Real.sqrt (q^2-1))⁻¹:ℂ)‖=(Real.sqrt (q^2-1))⁻¹ := by
      rw [← Complex.ofReal_inv,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    rw [hn,div_eq_mul_inv,mul_comm C]
    exact mul_le_mul hi (hb _) (norm_nonneg _) (inv_nonneg.mpr hsδ.le)

/-- A concrete first-derivative test bound for the actual geometric operator.
The constant is uniform over tests with a fixed positive support interval. -/
theorem positiveTimeAbelOperator_derivative_bound (N : ℕ) [NeZero N]
    (ψ : PositiveTimeTest) (C : ℝ) (hb : ∀ t,‖deriv ψ.toFun t‖≤C) :
    ‖positiveTimeAbelOperator N ψ‖≤
      2*Real.pi*((Real.sqrt 2/Real.pi)*((C/Real.sinh ψ.left)*(Real.cosh ψ.right+1))*
        (Real.cosh ψ.right-1)) :=
  abelKernelOperator_derivative_bound N ψ.lift ψ.lift_smooth ψ.lift_compact
    ψ.right ψ.right_nonneg ψ.lift_support (C/Real.sinh ψ.left)
    (coshTestLift_deriv_bound ψ.toFun ψ.smooth ψ.left ψ.right C ψ.left_pos ψ.support hb)

#print axioms coshTestLift_deriv
#print axioms coshTestLift_deriv_bound
#print axioms positiveTimeAbelOperator_derivative_bound

end QuantitativeMaass
