module

public import QuantitativeMaassCutoffWordCountV1
public import QuantitativeMaassGrowingBandWidthV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass.Weighted

theorem eight_pow_le_root_exponential (a t : ℝ) (n : ℕ)
    (hn : (n:ℝ)≤a*fourthRootScale t) :
    (8:ℝ)^n≤Real.exp ((a*Real.log 8)*fourthRootScale t) := by
  have hlog : 0≤Real.log 8 := Real.log_nonneg (by norm_num)
  have he : (8:ℝ)^n=Real.exp ((n:ℝ)*Real.log 8) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<8)]
  rw [he]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_right hn hlog]

/-- All intermediate bands for words of length O(fourthRootScale t)
remain sublinear, uniformly over the allowed word length. -/
theorem cutoffWordRadius_uniform_quarter (a D : ℝ) (ha : 0≤a) (hD : 0≤D) :
    ∀ᶠ t in atTop,∀ n : ℕ,(n:ℝ)≤a*fourthRootScale t →
      cutoffWordRadius (Real.exp (D*fourthRootScale t)) n≤t/4 := by
  let K := a+D+4
  have hK : 0≤K := by dsimp only [K]; linarith
  filter_upwards [exponential_band_width_quarter K hK,
    fourthRootScale_tendsto.eventually (eventually_ge_atTop (1:ℝ))] with t ht hroot
  intro n hn
  let L := Real.exp (D*fourthRootScale t)
  have hL : 1≤L := Real.one_le_exp (mul_nonneg hD (by linarith))
  have hnexp : (n:ℝ)+1≤Real.exp (a*fourthRootScale t) :=
    (Real.add_one_le_exp (n:ℝ)).trans (Real.exp_le_exp.mpr hn)
  have hR : cutoffWordRadius L n≤4*((n:ℝ)+1)*L := by
    rw [cutoffWordRadius_eq]
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) (show 0≤L-1 by linarith)]
  have hfour : 4≤Real.exp (4*fourthRootScale t) := by
    have hh := Real.add_one_le_exp (4*fourthRootScale t)
    linarith
  apply (hR.trans _).trans ht.2
  calc
    _ ≤ Real.exp (4*fourthRootScale t)*Real.exp (a*fourthRootScale t)*L := by gcongr
    _ = Real.exp (K*fourthRootScale t) := by
      dsimp only [L,K]
      rw [←Real.exp_add,←Real.exp_add]
      congr 1
      ring

#print axioms eight_pow_le_root_exponential
#print axioms cutoffWordRadius_uniform_quarter

end QuantitativeMaass.Weighted
