module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalDiscriminant

open UpperHalfPlane Filter Complex
open scoped Topology Real

/-- The nonvanishing factor after removing the first q power from Delta. -/
def factor (z : ℍ) : ℂ := ∏' n : ℕ, (1 - ModularForm.eta_q n z) ^ 24

theorem factor_ne_zero (z : ℍ) : factor z ≠ 0 := by
  have hn := ModularForm.discriminant_ne_zero z
  rw [ModularForm.discriminant_eq_q_prod] at hn
  exact (mul_ne_zero_iff.mp hn).2

theorem factor_tendsto : Tendsto factor atImInfty (𝓝 1) :=
  ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow

theorem log_norm_eq (z : ℍ) :
    Real.log ‖ModularForm.discriminant z‖ = -2 * Real.pi * z.im + Real.log ‖factor z‖ := by
  rw [ModularForm.discriminant_eq_q_prod, norm_mul]
  change Real.log (‖Function.Periodic.qParam 1 z‖ * ‖factor z‖) = _
  rw [Real.log_mul (norm_ne_zero_iff.mpr (by simp [Function.Periodic.qParam]))
      (norm_ne_zero_iff.mpr (factor_ne_zero z))]
  have hq : ‖Function.Periodic.qParam 1 z‖ = Real.exp (-2 * Real.pi * z.im) := by
    simp [Function.Periodic.qParam, Complex.norm_exp]
  rw [hq, Real.log_exp]

/-- The exact exponential decay rate, expressed without a choice of
 vertical path. -/
theorem log_norm_div_im_tendsto :
    Tendsto (fun z : ℍ => Real.log ‖ModularForm.discriminant z‖ / z.im)
      atImInfty (𝓝 (-2 * Real.pi)) := by
  have him : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
  have hp : Tendsto (fun z : ℍ => Real.log ‖factor z‖) atImInfty (𝓝 0) := by
    simpa only [norm_one, Real.log_one] using factor_tendsto.norm.log (by simp)
  have hsmall := hp.div_atTop him
  have he (z : ℍ) : Real.log ‖ModularForm.discriminant z‖ / z.im =
      -2 * Real.pi + Real.log ‖factor z‖ / z.im := by
    rw [log_norm_eq, add_div, mul_div_cancel_right₀ _ z.im_ne_zero]
  simp_rw [he]
  simpa using tendsto_const_nhds.add hsmall

#print axioms factor_ne_zero
#print axioms factor_tendsto
#print axioms log_norm_eq
#print axioms log_norm_div_im_tendsto

end AsymptoticClassicalDiscriminant
