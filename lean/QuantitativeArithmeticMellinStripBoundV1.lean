module
public import Mathlib.Analysis.MellinTransform
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticMellinStrip
open Complex Set MeasureTheory

theorem kernel_norm (R : ℝ → ℂ) (s : ℂ) (t : ℝ) (ht : 0<t) :
    ‖(t:ℂ)^(s-1)*R t‖=t^(s.re-1)*‖R t‖ := by
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp only [Complex.sub_re,Complex.one_re]

theorem kernel_le_endpoints (R : ℝ → ℂ) (a b : ℝ) (s : ℂ)
    (ha : a≤s.re) (hb : s.re≤b) (t : ℝ) (ht : 0<t) :
    ‖(t:ℂ)^(s-1)*R t‖≤‖(t:ℂ)^((a:ℂ)-1)*R t‖+‖(t:ℂ)^((b:ℂ)-1)*R t‖ := by
  rw [kernel_norm R s t ht,kernel_norm R (a:ℂ) t ht,kernel_norm R (b:ℂ) t ht]
  simp only [Complex.ofReal_re]
  by_cases ht1 : 1≤t
  · have hp := Real.rpow_le_rpow_of_exponent_le ht1 (sub_le_sub_right hb 1)
    have hh := mul_le_mul_of_nonneg_right hp (norm_nonneg (R t))
    exact hh.trans (le_add_of_nonneg_left (by positivity))
  · have hp := Real.rpow_le_rpow_of_exponent_ge ht (le_of_not_ge ht1) (sub_le_sub_right ha 1)
    have hh := mul_le_mul_of_nonneg_right hp (norm_nonneg (R t))
    exact hh.trans (le_add_of_nonneg_right (by positivity))

/-- Absolute Mellin convergence on two real lines gives a uniform bound
on the entire closed strip, without smoothness of the cutoff. -/
theorem bounded_strip (R : ℝ → ℂ) (a b : ℝ)
    (ha : MellinConvergent R (a:ℂ)) (hb : MellinConvergent R (b:ℂ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ s : ℂ,a≤s.re → s.re≤b → ‖mellin R s‖≤C := by
  let A : ℝ → ℝ := fun t => ‖(t:ℂ)^((a:ℂ)-1)*R t‖
  let B : ℝ → ℝ := fun t => ‖(t:ℂ)^((b:ℂ)-1)*R t‖
  have hA : IntegrableOn A (Ioi 0) := by
    simpa only [A,IntegrableOn,MellinConvergent,smul_eq_mul] using ha.norm
  have hB : IntegrableOn B (Ioi 0) := by
    simpa only [B,IntegrableOn,MellinConvergent,smul_eq_mul] using hb.norm
  refine ⟨∫ t in Ioi (0:ℝ), A t+B t, integral_nonneg (fun t => add_nonneg (norm_nonneg _) (norm_nonneg _)),?_⟩
  intro s hsa hsb
  change ‖∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*R t‖≤_
  apply norm_integral_le_of_norm_le (hA.add hB)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact kernel_le_endpoints R a b s hsa hsb t ht
#print axioms bounded_strip
end QuantitativeArithmeticMellinStrip
