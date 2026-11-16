module

public import QuantitativeMaassGeometricLimitV1
public import QuantitativeMaassExceptionalWindowLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- Exact exponential saving at the logarithmic scale. -/
theorem exp_half_log_le_sqrt_eventually :
    ∀ᶠ t : ℝ in atTop,Real.exp (Real.log t/2)≤Real.sqrt t := by
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have heq : (Real.exp (Real.log t/2))^2=t := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(Real.log t/2)=Real.log t by ring,Real.exp_log ht]
  nlinarith [Real.sq_sqrt ht.le,Real.sqrt_nonneg t,Real.exp_pos (Real.log t/2)]

/-- Exponential geometric costs in two radii negligible relative to the logarithmic
scale are absorbed by the actual square-root spectral saving. -/
theorem geometric_majorant_log_tendsto (ε R L : ℝ → ℝ) (A C : ℝ)
    (hA : 0≤A) (hC : 0≤C) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hRp : ∀ᶠ t in atTop,0≤R t) (hLp : ∀ᶠ t in atTop,0≤L t)
    (hR : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0))
    (hL : Tendsto (fun t => L t/Real.log t) atTop (𝓝 0)) :
    Tendsto (fun t => C*Real.sqrt t*(ε t)^2*Real.exp (A*R t+30*L t)/(t*ε t))
      atTop (𝓝 0) := by
  have hsum : Tendsto (fun t => (R t+L t)/Real.log t) atTop (𝓝 0) := by
    simpa only [add_div,add_zero] using hR.add hL
  have hex := propagation_excess_tendsto Real.log (fun _ : ℝ => (1:ℝ))
    (fun t => R t+L t) (A+30) (1/2) (by positivity) (by norm_num)
    Real.tendsto_log_atTop (Eventually.of_forall (fun _ => zero_lt_one))
    (by simpa only [one_mul] using Real.tendsto_log_atTop) hsum
  have hm : Tendsto (fun t => C*Real.exp ((A+30)*(R t+L t)-Real.log t/2)) atTop (𝓝 0) := by
    simpa only [div_one,one_div,mul_zero,inv_mul_eq_div] using hex.const_mul C
  apply squeeze_zero' _ _ hm
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    have hεpos : 0<ε t := he.1
    positivity
  · filter_upwards [hε,hRp,hLp,exp_half_log_le_sqrt_eventually,
      eventually_gt_atTop (0:ℝ)] with t he hr hl hs ht
    have hst : 0<Real.sqrt t := Real.sqrt_pos.mpr ht
    have hcancel : Real.sqrt t/t=1/Real.sqrt t := by
      apply (div_eq_div_iff ht.ne' hst.ne').mpr
      nlinarith [Real.sq_sqrt ht.le]
    have heA : A*R t+30*L t≤(A+30)*(R t+L t) := by nlinarith
    calc
      _ = C*(ε t)*Real.exp (A*R t+30*L t)*(Real.sqrt t/t) := by
        field_simp [he.1.ne']
      _ = C*(ε t)*Real.exp (A*R t+30*L t)/Real.sqrt t := by rw [hcancel];ring
      _ ≤ C*Real.exp ((A+30)*(R t+L t))/Real.exp (Real.log t/2) := by
        apply div_le_div₀ (by positivity) _ (Real.exp_pos _) hs
        calc
          _ ≤ C*Real.exp (A*R t+30*L t) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left he.2 hC) (Real.exp_pos (A*R t+30*L t)).le
          _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr heA) hC
      _ = _ := by rw [Real.exp_sub];ring

#print axioms exp_half_log_le_sqrt_eventually
#print axioms geometric_majorant_log_tendsto

end QuantitativeMaass
