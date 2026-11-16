module

public import QuantitativeMaassUpperErrorLimitsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Exact cancellation of the main-term normalization in the full cusp-tail error. -/
theorem upper_tail_error_identity (C B R t ε : ℝ) (ht : 0<t) (hε : 0<ε) :
    (C*R^3*ε^2*t*Real.sqrt t*Real.exp (B*R)/upperCuspHeight t)/(t*ε)=
      C*R^3*ε*Real.exp (B*R-Real.log t/4) := by
  have hs : Real.sqrt t=Real.exp (Real.log t/2) := by rw [Real.exp_half,Real.exp_log ht]
  calc
    _ = C*R^3*ε*(Real.sqrt t*Real.exp (B*R)/upperCuspHeight t) := by
      field_simp
    _ = _ := by
      rw [hs,upperCuspHeight,←Real.exp_add,←Real.exp_sub]
      congr 1
      congr 1
      ring

/-- The polynomial radius factor costs only a further fixed exponential. -/
theorem radius_cube_exp_le (R : ℝ) (hR : 0≤R) : R^3≤Real.exp (3*R) := by
  have hh : R≤Real.exp R := by linarith [Real.add_one_le_exp R]
  have hp := pow_le_pow_left₀ hR hh 3
  simpa only [←Real.exp_nat_mul,Nat.cast_ofNat] using hp

/-- The full actual tail majorant is negligible with the same propagation schedule. -/
theorem upper_tail_error_tendsto (ε R : ℝ → ℝ) (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1) (hRp : ∀ᶠ t in atTop,0≤R t)
    (hR : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0)) :
    Tendsto (fun t => (C*(R t)^3*(ε t)^2*t*Real.sqrt t*Real.exp (B*R t)/upperCuspHeight t)/(t*ε t))
      atTop (𝓝 0) := by
  have hm := (sublog_exp_saving R (B+3) (1/4) (by positivity) (by norm_num) hR).const_mul C
  simp only [mul_zero] at hm
  apply squeeze_zero' _ _ hm
  · filter_upwards [hε,hRp,eventually_gt_atTop (0:ℝ)] with t he hr ht
    have hY := upperCuspHeight_pos t
    exact div_nonneg (by positivity) (mul_pos ht he.1).le
  · filter_upwards [hε,hRp,eventually_gt_atTop (0:ℝ)] with t he hr ht
    have hεpos : 0<ε t := he.1
    rw [upper_tail_error_identity C B (R t) t (ε t) ht he.1]
    calc
      _ ≤ C*Real.exp (3*R t)*1*Real.exp (B*R t-Real.log t/4) := by
        gcongr
        · exact radius_cube_exp_le (R t) hr
        · exact he.2
      _ = C*Real.exp ((B+3)*R t-(1/4)*Real.log t) := by
        rw [mul_one,mul_assoc,←Real.exp_add]
        congr 2
        ring

#print axioms upper_tail_error_identity
#print axioms radius_cube_exp_le
#print axioms upper_tail_error_tendsto

end QuantitativeMaass
