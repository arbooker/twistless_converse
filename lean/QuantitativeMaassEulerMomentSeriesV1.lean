module

public import QuantitativeMaassEulerDecayV1
public import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Explicit derivative majorant on every positive-height half-plane. -/
def principalMomentMajorant (b : ℕ → ℂ) (j k : ℕ) (c a : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (c*a)*MaassKBessel.moment j 0 (c*a))*
    (‖b (n+1)‖*((n+1:ℕ):ℝ)^k*Real.exp (-(c*a)*((n+1:ℕ):ℝ)))

theorem principalMomentMajorant_summable {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (j k : ℕ) (c a : ℝ) (hc : 0<c) (ha : 0<a) :
    Summable (principalMomentMajorant b j k c a) :=
  (polynomialGrowth_exp_summable hb k (c*a) (mul_pos hc ha)).mul_left _

/-- All coefficient-weighted Bessel moments admit one summable majorant
uniformly in x and in heights y>=a. The order j and polynomial weight k are arbitrary. -/
theorem principalMomentMajorant_bound (b : ℕ → ℂ) (j k : ℕ) (r c a : ℝ)
    (hc : 0<c) (ha : 0<a) (n : ℕ) (y : ℝ) (hy : a≤y) :
    ‖b (n+1)‖*((n+1:ℕ):ℝ)^k*‖MaassKBessel.moment j r (c*((n+1:ℕ):ℝ)*y)‖≤
      principalMomentMajorant b j k c a n := by
  have hn : (1:ℝ)≤((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hy0 : 0<y := ha.trans_le hy
  have hbase : c*a≤c*((n+1:ℕ):ℝ)*y := by
    calc
      c*a ≤ c*y := mul_le_mul_of_nonneg_left hy hc.le
      _ = c*1*y := by ring
      _ ≤ _ := by gcongr
  have hh := bessel_moment_decay_from j r (c*a) (c*((n+1:ℕ):ℝ)*y) (mul_pos hc ha) hbase
  have hdec : Real.exp (c*a-c*((n+1:ℕ):ℝ)*y)≤
      Real.exp (c*a)*Real.exp (-(c*a)*((n+1:ℕ):ℝ)) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hy (show 0≤c*((n+1:ℕ):ℝ) by positivity)]
  calc
    _ ≤ (‖b (n+1)‖*((n+1:ℕ):ℝ)^k)*
        ((Real.exp (c*a)*Real.exp (-(c*a)*((n+1:ℕ):ℝ)))*MaassKBessel.moment j 0 (c*a)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hh.trans (mul_le_mul_of_nonneg_right hdec (MaassKBessel.zero_moment_nonneg _ _))
    _ = _ := by unfold principalMomentMajorant; ring

/-- Absolute convergence for all weighted moment series follows directly from
the original individual coefficient growth condition. -/
theorem principal_moment_series_summable {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (j k : ℕ) (r c y : ℝ) (hc : 0<c) (hy : 0<y) :
    Summable (fun n : ℕ => ‖b (n+1)‖*((n+1:ℕ):ℝ)^k*
      ‖MaassKBessel.moment j r (c*((n+1:ℕ):ℝ)*y)‖) := by
  apply (principalMomentMajorant_summable hb j k c y hc hy).of_nonneg_of_le
    (fun _ => by positivity)
  intro n
  exact principalMomentMajorant_bound b j k r c y hc hy n y le_rfl

#print axioms principalMomentMajorant_summable
#print axioms principalMomentMajorant_bound
#print axioms principal_moment_series_summable

end QuantitativeMaass
