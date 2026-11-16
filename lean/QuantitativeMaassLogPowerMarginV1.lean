module

public import QuantitativeMaassLogPowerRadiusV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace QuantitativeMaass

/-- The square-root relation holds globally, including the max-one convention. -/
theorem logPowerRadius_half_square (c t : ℝ) :
    logPowerRadius c t=(logPowerRadius (c/2) t)^2 := by
  have he : Real.exp (c*Real.log (Real.log t))=(Real.exp ((c/2)*Real.log (Real.log t)))^2 := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  unfold logPowerRadius
  rw [he]
  by_cases h : 1≤Real.exp ((c/2)*Real.log (Real.log t))
  · rw [max_eq_right h,max_eq_right (by nlinarith)]
  · have hh : Real.exp ((c/2)*Real.log (Real.log t))≤1 := le_of_not_ge h
    have hs := pow_le_pow_left₀ (Real.exp_pos _).le hh 2
    rw [max_eq_left hh,max_eq_left (by simpa only [one_pow] using hs),one_pow]

/-- A globally positive trimming margin at a fixed logarithmic-power radius. -/
def logPowerMargin (c t : ℝ) : ℝ := 1/logPowerRadius (c/2) t

theorem logPowerMargin_pos (c t : ℝ) : 0<logPowerMargin c t :=
  one_div_pos.mpr (logPowerRadius_pos _ _)

theorem logPowerMargin_le_one (c t : ℝ) : logPowerMargin c t≤1 := by
  apply (div_le_one (logPowerRadius_pos _ _)).mpr
  exact le_max_left _ _

theorem logPowerRadius_mul_margin (c t : ℝ) :
    logPowerRadius c t*logPowerMargin c t=logPowerRadius (c/2) t := by
  rw [logPowerRadius_half_square c t]
  dsimp only [logPowerMargin]
  field_simp [(logPowerRadius_pos (c/2) t).ne']

theorem logPowerMargin_tendsto (c : ℝ) (hc : 0<c) :
    Tendsto (logPowerMargin c) atTop (𝓝 0) := by
  change Tendsto (fun t => 1/logPowerRadius (c/2) t) atTop (𝓝 0)
  simpa only [one_div,Function.comp_def] using
    tendsto_inv_atTop_zero.comp (logPowerRadius_tendsto (c/2) (by positivity))

/-- The margin is negligible relative to every width satisfying the original
triple-logarithmic resolution hypothesis. -/
theorem logPowerMargin_div_width (c : ℝ) (hc : 0<c) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => logPowerMargin c t/ε t) atTop (𝓝 0) := by
  have hh := tendsto_inv_atTop_zero.comp
    (logPowerRadius_resolves_width (c/2) (by positivity) ε hε hproduct)
  simpa [logPowerMargin,Function.comp_def,div_eq_mul_inv,mul_comm] using hh

/-- The actual propagation times trimming margin diverges. -/
theorem logPowerRadius_margin_tendsto (c : ℝ) (hc : 0<c) :
    Tendsto (fun t => logPowerRadius c t*logPowerMargin c t) atTop atTop := by
  simpa only [logPowerRadius_mul_margin] using logPowerRadius_tendsto (c/2) (by positivity : 0<c/2)

#print axioms logPowerRadius_half_square
#print axioms logPowerMargin_pos
#print axioms logPowerMargin_le_one
#print axioms logPowerRadius_mul_margin
#print axioms logPowerMargin_tendsto
#print axioms logPowerMargin_div_width
#print axioms logPowerRadius_margin_tendsto

end QuantitativeMaass
