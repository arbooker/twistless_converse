module

public import QuantitativeMaassWeightedMomentDecayV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass

theorem fourthRootScale_tendsto : Tendsto fourthRootScale atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp slowScale_tendsto)

theorem fourthRootScale_pow_four {t : ℝ} (ht : 0≤slowScale t) :
    (fourthRootScale t)^4=slowScale t := by
  unfold fourthRootScale
  calc
    _ = ((Real.sqrt (Real.sqrt (slowScale t)))^2)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt ht]

/-- The weighted exceptional estimate also absorbs an additional inverse
window width under precisely the original shrinking-window condition. -/
theorem fourthRoot_exponential_div_width (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (-fourthRootScale t)/ε t) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 1 (by norm_num)).comp
    fourthRootScale_tendsto
  have hm : Tendsto (fun t => (fourthRootScale t)^4*Real.exp (-fourthRootScale t))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat,neg_mul,one_mul,Function.comp_def] using hh
  apply squeeze_zero' _ _ hm
  · filter_upwards [hε] with t he
    positivity
  · filter_upwards [hε,hproduct.eventually (eventually_ge_atTop (1:ℝ)),
      slowScale_tendsto.eventually (eventually_ge_atTop (0:ℝ))] with t he hp ht
    rw [fourthRootScale_pow_four ht]
    apply (div_le_iff₀ he).mpr
    have h := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-fourthRootScale t)).le
    nlinarith only [h]

/-- A weighted squared-error limit remains valid with two inverse
window widths, as needed when passing to trace errors by Cauchy--Schwarz. -/
theorem weighted_energy_two_widths (ε E : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hE : Tendsto (fun t => Real.exp (fourthRootScale t)*E t/(t*ε t)) atTop (𝓝 0)) :
    Tendsto (fun t => E t/(t*(ε t)^2)) atTop (𝓝 0) := by
  have hh := hE.mul (fourthRoot_exponential_div_width ε hε hproduct)
  simp only [mul_zero] at hh
  convert hh using 1
  funext t
  rw [div_mul_div_comm]
  have hn : Real.exp (fourthRootScale t)*E t*Real.exp (-fourthRootScale t)=E t := by
    calc
      _ = E t*(Real.exp (fourthRootScale t)*Real.exp (-fourthRootScale t)) := by ring
      _ = _ := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  rw [hn]
  congr 1
  ring

#print axioms fourthRootScale_tendsto
#print axioms fourthRootScale_pow_four
#print axioms fourthRoot_exponential_div_width
#print axioms weighted_energy_two_widths

end QuantitativeMaass
