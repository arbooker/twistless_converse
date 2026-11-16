module

public import QuantitativeMaassWeightedEulerV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- A uniform exponential factor can be extracted from every weighted actual
Bessel moment while retaining a summable majorant at half the lower height. -/
theorem principalMoment_exponential_bound (b : ℕ → ℂ) (j k : ℕ) (r c a : ℝ)
    (hc : 0<c) (ha : 0<a) (n : ℕ) (y : ℝ) (hy : a≤y) :
    ‖b (n+1)‖*((n+1:ℕ):ℝ)^k*‖MaassKBessel.moment j r (c*((n+1:ℕ):ℝ)*y)‖≤
      Real.exp (-(c*y)/2)*principalMomentMajorant b j k c (a/2) n := by
  have hy0 : 0<y := ha.trans_le hy
  have hn : (1:ℝ)≤((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hp : 0<c*((n+1:ℕ):ℝ)*(y/2) := by positivity
  have hd := bessel_moment_decay_from j r (c*((n+1:ℕ):ℝ)*(y/2))
    (c*((n+1:ℕ):ℝ)*y) hp (by nlinarith)
  have he : Real.exp (c*((n+1:ℕ):ℝ)*(y/2)-c*((n+1:ℕ):ℝ)*y)≤Real.exp (-(c*y)/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hn (mul_pos hc hy0).le]
  have ht := hd.trans (mul_le_mul_of_nonneg_right he (MaassKBessel.zero_moment_nonneg j _))
  have hm := principalMomentMajorant_bound b j k 0 c (a/2) hc (by positivity) n (y/2) (by linarith)
  simp only [Real.norm_eq_abs,abs_of_nonneg (MaassKBessel.zero_moment_nonneg j _)] at hm
  calc
    _ ≤ (‖b (n+1)‖*((n+1:ℕ):ℝ)^k)*
        (Real.exp (-(c*y)/2)*MaassKBessel.moment j 0 (c*((n+1:ℕ):ℝ)*(y/2))) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = Real.exp (-(c*y)/2)*(‖b (n+1)‖*((n+1:ℕ):ℝ)^k*
        MaassKBessel.moment j 0 (c*((n+1:ℕ):ℝ)*(y/2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le

theorem principalWeightedTerm_exponential_bound (b : ℕ → ℂ) (r : ℝ) (j k σ n : ℕ)
    (a : ℝ) (ha : 0<a) (x y : ℝ) (hy : a≤y) :
    ‖principalWeightedTerm b r j k σ n (x,y)‖≤
      (2*Real.exp (-Real.pi*y))*principalMomentMajorant b j k (2*Real.pi) (a/2) n := by
  unfold principalWeightedTerm
  rw [norm_mul,norm_mul,norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_real]
  have hm := principalMoment_exponential_bound b j k r (2*Real.pi) a (by positivity) ha n y hy
  rw [show -((2*Real.pi)*y)/2= -Real.pi*y by ring] at hm
  calc
    _ ≤ (‖b (n+1)‖*((n+1:ℕ):ℝ)^k*‖MaassKBessel.moment j r (2*Real.pi*((n+1:ℕ):ℝ)*y)‖)*2 := by
      gcongr
      exact eulerParityPhase_norm_le σ (n+1) x
    _ ≤ _ := by nlinarith

theorem principalWeightedSeries_exponential_bound {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (r : ℝ) (j k σ : ℕ)
    (a : ℝ) (ha : 0<a) (x y : ℝ) (hy : a≤y) :
    ‖principalWeightedSeries b r j k σ (x,y)‖≤
      (2*Real.exp (-Real.pi*y))*(∑' n,principalMomentMajorant b j k (2*Real.pi) (a/2) n) := by
  have hs := (principalMomentMajorant_summable hb j k (2*Real.pi) (a/2) (by positivity) (by positivity)).mul_left
    (2*Real.exp (-Real.pi*y))
  have hn : Summable (fun n => ‖principalWeightedTerm b r j k σ n (x,y)‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => principalWeightedTerm_exponential_bound b r j k σ n a ha x y hy)
  calc
    _ ≤ ∑' n,‖principalWeightedTerm b r j k σ n (x,y)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n,(2*Real.exp (-Real.pi*y))*principalMomentMajorant b j k (2*Real.pi) (a/2) n :=
      Summable.tsum_le_tsum (fun n => principalWeightedTerm_exponential_bound b r j k σ n a ha x y hy) hn hs
    _ = _ := tsum_mul_left

#print axioms principalMoment_exponential_bound
#print axioms principalWeightedTerm_exponential_bound
#print axioms principalWeightedSeries_exponential_bound

end QuantitativeMaass
