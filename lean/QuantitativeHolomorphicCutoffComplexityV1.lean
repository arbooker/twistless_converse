module

public import QuantitativeHolomorphicSimultaneousCutoffsV1

set_option autoImplicit false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

/-- Binary depth itself is logarithmic, not merely bounded by its argument. -/
theorem binaryDepth_le_log {x : ℝ} (hx : 0≤x) :
    (binaryDepth x:ℝ)≤Real.log (2*(x+2))/Real.log 2 := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hp := binaryDepth_power_upper x hx
  have h := Real.log_le_log (by positivity : 0<(2:ℝ)^binaryDepth x) hp
  rw [Real.log_pow] at h
  exact (le_div_iff₀ hlog).mpr h

/-- The actual Newton perturbation amplification grows exponentially in the
square of its binary threshold. This is the cost needed by the simultaneous
cutoffs, rather than an assumed error decay. -/
theorem amplification_binaryDepth_le {x : ℝ} (hx : 0≤x) :
    amplification (binaryDepth x)≤Real.exp (4*(3+Real.log 7)*(x+2)^2) := by
  let n := binaryDepth x
  let a := 4*(x+2)^2
  have ha : 0≤a := by dsimp [a]; positivity
  have h4 : (4:ℝ)^n≤a := binaryDepth_complexity x hx
  have h3 : (3:ℝ)^n≤a :=
    (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) (by norm_num : (3:ℝ)≤4) n).trans h4
  have hfirst : (1+3*(3^n:ℕ):ℝ)≤Real.exp (3*a) := by
    have h : 3*a+1≤Real.exp (3*a) := Real.add_one_le_exp _
    push_cast
    nlinarith only [h3,h]
  have hlog : 0≤Real.log 7 := Real.log_nonneg (by norm_num)
  have hsecond : (7:ℝ)^(4^n)≤Real.exp (a*Real.log 7) := by
    calc
      _ = Real.exp ((4^n:ℕ)*Real.log 7) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<7)]
      _ ≤ _ := Real.exp_le_exp.mpr (by exact_mod_cast mul_le_mul_of_nonneg_right h4 hlog)
  have h := mul_le_mul hfirst hsecond (by positivity) (Real.exp_nonneg _)
  apply h.trans_eq
  rw [←Real.exp_add]
  congr 1
  dsimp [a]
  ring

#print axioms binaryDepth_le_log
#print axioms amplification_binaryDepth_le

end QuantitativeHolomorphic.Schedule
