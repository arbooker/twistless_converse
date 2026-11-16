module

public import QuantitativeMaassLogPowerRadiusV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Actual cusp cutoff, growing strictly between the square-root and linear scales. -/
def upperCuspHeight (t : ℝ) : ℝ := Real.exp (3*Real.log t/4)

theorem upperCuspHeight_pos (t : ℝ) : 0<upperCuspHeight t := Real.exp_pos _

theorem upperCuspHeight_tendsto : Tendsto upperCuspHeight atTop atTop := by
  apply Real.tendsto_exp_atTop.comp
  convert Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0:ℝ)<3/4) using 1
  ext t
  ring

/-- Every sublogarithmic propagation radius eventually lies below the chosen tail. -/
theorem upperCuspHeight_admissible (R : ℝ → ℝ) (H : ℝ)
    (hH : 0<H) (hR : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0)) :
    ∀ᶠ t in atTop,2≤upperCuspHeight t ∧ H*R t<Real.log (upperCuspHeight t) := by
  filter_upwards [upperCuspHeight_tendsto.eventually (eventually_ge_atTop (2:ℝ)),
    hR.eventually (gt_mem_nhds (by positivity : (0:ℝ)<3/(4*H))),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t hy hr ht
  refine ⟨hy,?_⟩
  rw [upperCuspHeight,Real.log_exp]
  have hh := (div_lt_iff₀ ht).mp hr
  have hcoef : H*(3/(4*H))=3/4 := by field_simp
  nlinarith [mul_lt_mul_of_pos_left hh hH]

/-- Any fixed exponential cost in a sublogarithmic radius loses against a
positive power of the spectral centre. -/
theorem sublog_exp_saving (R : ℝ → ℝ) (A d : ℝ) (hA : 0≤A) (hd : 0<d)
    (hR : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0)) :
    Tendsto (fun t => Real.exp (A*R t-d*Real.log t)) atTop (𝓝 0) := by
  have hh := propagation_excess_tendsto Real.log (fun _ : ℝ => (1:ℝ)) R A d hA hd
    Real.tendsto_log_atTop (Eventually.of_forall (fun _ => zero_lt_one))
    (by simpa only [one_mul] using Real.tendsto_log_atTop) hR
  simpa only [div_one] using hh

/-- Exact normalized core error at the chosen height. -/
theorem upper_core_error_identity (C A R t ε : ℝ) (ht : 0<t) (hε : 0<ε) :
    C*Real.sqrt t*ε^2*Real.exp (A*R)*(1+Real.sqrt (upperCuspHeight t))/(t*ε)=
      C*ε*(Real.exp (A*R-Real.log t/2)+Real.exp (A*R-Real.log t/8)) := by
  have hs : Real.sqrt t=Real.exp (Real.log t/2) := by rw [Real.exp_half,Real.exp_log ht]
  have hy : Real.sqrt (upperCuspHeight t)=Real.exp (3*Real.log t/8) := by
    rw [upperCuspHeight,←Real.exp_half]
    congr 1
    ring
  have heq : Real.exp (Real.log t/2)/t=Real.exp (-Real.log t/2) := by
    rw [show -Real.log t/2=Real.log t/2-Real.log t by ring,Real.exp_sub,Real.exp_log ht]
  calc
    _ = C*ε*(Real.exp (Real.log t/2)/t)*Real.exp (A*R)*(1+Real.exp (3*Real.log t/8)) := by
      rw [hs,hy]
      field_simp
    _ = _ := by
      have hfirst : Real.exp (-Real.log t/2)*Real.exp (A*R)=Real.exp (A*R-Real.log t/2) := by
        rw [←Real.exp_add]
        congr 1
        ring
      have hsecond : Real.exp (A*R-Real.log t/2)*Real.exp (3*Real.log t/8)=Real.exp (A*R-Real.log t/8) := by
        rw [←Real.exp_add]
        congr 1
        ring
      rw [heq,mul_assoc (C*ε),hfirst,mul_add,mul_one,mul_assoc (C*ε),hsecond]
      ring

/-- Uniform normalized core error tends to zero without strengthening the width. -/
theorem upper_core_error_tendsto (ε R : ℝ → ℝ) (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hR : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0)) :
    Tendsto (fun t => C*Real.sqrt t*(ε t)^2*Real.exp (A*R t)*
      (1+Real.sqrt (upperCuspHeight t))/(t*ε t)) atTop (𝓝 0) := by
  have hm := ((sublog_exp_saving R A (1/2) hA (by norm_num) hR).add
    (sublog_exp_saving R A (1/8) hA (by norm_num) hR)).const_mul C
  simp only [add_zero,mul_zero] at hm
  apply squeeze_zero' _ _ hm
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    exact div_nonneg (by positivity) (mul_pos ht he.1).le
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    rw [upper_core_error_identity C A (R t) t (ε t) ht he.1]
    have hh := mul_le_mul_of_nonneg_left he.2 hC
    simpa only [mul_one,one_div_mul_eq_div] using mul_le_mul_of_nonneg_right hh
      (show 0≤Real.exp (A*R t-Real.log t/2)+Real.exp (A*R t-Real.log t/8) by positivity)

#print axioms upperCuspHeight_pos
#print axioms upperCuspHeight_tendsto
#print axioms upperCuspHeight_admissible
#print axioms sublog_exp_saving
#print axioms upper_core_error_identity
#print axioms upper_core_error_tendsto

end QuantitativeMaass
