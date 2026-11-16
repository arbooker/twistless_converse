module

public import QuantitativeMaassQuotientWeightFixedIndexV1
public import QuantitativeMaassCappedWeightV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticCompactBranch AsymptoticMassTransport
open scoped MatrixGroups Topology

namespace QuantitativeMaass

theorem strip_cap_square_dist (N : ℕ) {ε : ℝ} (hε : 0<ε)
    (v : ℕ) (z w : ℍ) (g : Strip N z) :
    cap ε v (g.val.val • z)^2≤Real.exp ((2*v:ℝ)*dist z w)*
      cap ε v (g.val.val • w)^2 := by
  have hd : dist (g.val.val • z) (g.val.val • w)=dist z w := by
    rw [←representative_label g.val,integralLabel_action,integralLabel_action]
    change dist (((representative g.val):SL(2,ℝ)) • z)
      (((representative g.val):SL(2,ℝ)) • w)=dist z w
    exact dist_smul _ _ _
  have hh := (div_le_iff₀ (cappedHeightWeight_pos hε (2*v) (g.val.val • w))).mp
    (cappedHeightWeight_ratio_bound hε (2*v) (g.val.val • z) (g.val.val • w))
  simpa only [cappedHeightWeight,cap,←pow_mul,Nat.mul_comm v 2,Nat.cast_mul,
    Nat.cast_ofNat,hd] using hh

/-- The actual orbit weight has exponential distortion controlled by
hyperbolic distance. The bound is independent of the cusp cap height. -/
theorem quotientWeight_dist_bound (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (z w : ℍ) :
    weight N ε v z≤Real.exp ((2*v:ℝ)*dist z w)*weight N ε v w := by
  rw [quotientWeight_fixed_index N z z,quotientWeight_fixed_index N z w]
  calc
    _ ≤ ∑' g : Strip N z,Real.exp ((2*v:ℝ)*dist z w)*cap ε v (g.val.val • w)^2 :=
      (quotientWeight_fixed_summable N z z hε hv).tsum_le_tsum
        (strip_cap_square_dist N hε v z w)
        ((quotientWeight_fixed_summable N z w hε hv).mul_left _)
    _ = _ := tsum_mul_left

/-- Summing the positive cap squares preserves their logarithmic
Lipschitz bound, even though the capped weight need not be smooth. -/
theorem quotientWeight_log_dist (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (z w : ℍ) :
    |Real.log (weight N ε v z)-Real.log (weight N ε v w)|≤(2*v:ℝ)*dist z w := by
  have hz := weight_pos N hε hv z
  have hw := weight_pos N hε hv w
  have hzw := quotientWeight_dist_bound N hε hv z w
  have hwz := quotientWeight_dist_bound N hε hv w z
  rw [←Real.exp_log hz,←Real.exp_log hw,←Real.exp_add,Real.exp_le_exp] at hzw
  rw [←Real.exp_log hw,←Real.exp_log hz,←Real.exp_add,Real.exp_le_exp,dist_comm w z] at hwz
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem quotientWeight_log_lipschitz (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    LipschitzWith (2*v:NNReal) (fun z => Real.log (weight N ε v z)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [Real.dist_eq,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast] using
    quotientWeight_log_dist N hε hv z w

#print axioms strip_cap_square_dist
#print axioms quotientWeight_dist_bound
#print axioms quotientWeight_log_dist
#print axioms quotientWeight_log_lipschitz

end QuantitativeMaass
