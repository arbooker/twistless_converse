module

public import QuantitativeMaassNewtonSourceCostV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter QuantitativeHolomorphic
open scoped Topology
namespace QuantitativeMaass

/-- The product of the actual local-filter degree and Newton cost exponent
is still negligible relative to the original slow scale. -/
theorem growingMomentDegree_newton_cost_sublinear :
    Tendsto (fun t => (growingMomentDegree t:ℝ)*(4:ℝ)^(bandNewtonDepth t)/slowScale t)
      atTop (𝓝 0) := by
  have hlim := (fourthRootScale_div_sqrt.add fourthRootScale_div_scale).const_mul 2
  simp only [add_zero,mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with t ht
    positivity
  · filter_upwards [slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ)),bandNewtonDepth_cost_bound] with t ht hn
    have hm : (growingMomentDegree t:ℝ)≤Real.sqrt (slowScale t)+1 :=
      (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
    have hs : 0<Real.sqrt (slowScale t) := Real.sqrt_pos.mpr ht
    have hc : Real.sqrt (slowScale t)*fourthRootScale t/slowScale t=
        fourthRootScale t/Real.sqrt (slowScale t) := by
      apply (div_eq_div_iff ht.ne' hs.ne').mpr
      have hh := congrArg (fun x : ℝ => x*fourthRootScale t) (Real.sq_sqrt ht.le)
      nlinarith only [hh]
    calc
      _ ≤ (Real.sqrt (slowScale t)+1)*(2*fourthRootScale t)/slowScale t := by
        apply div_le_div_of_nonneg_right _ ht.le
        exact mul_le_mul hm hn (by positivity) (by positivity)
      _ = 2*(Real.sqrt (slowScale t)*fourthRootScale t/slowScale t+fourthRootScale t/slowScale t) := by ring
      _ = _ := by rw [hc]

/-- The actual composed polynomial word degree has the same sublinear
bound, including the identity terms in every factor. -/
theorem growingMomentDegree_newton_degree_sublinear :
    Tendsto (fun t => ((growingMomentDegree t:ℝ)+1)*
      (((inverseSqrtPolynomial (bandNewtonDepth t)).natDegree:ℝ)+1)/slowScale t)
      atTop (𝓝 0) := by
  have hlim := growingMomentDegree_newton_cost_sublinear.add (fourthRootScale_div_scale.const_mul 2)
  simp only [mul_zero,add_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with t ht
    positivity
  · filter_upwards [slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ)),bandNewtonDepth_cost_bound] with t ht hn
    have hd : ((inverseSqrtPolynomial (bandNewtonDepth t)).natDegree:ℝ)+1≤(4:ℝ)^(bandNewtonDepth t) := by
      have hh := (inverseSqrtPolynomial_degree_bound (bandNewtonDepth t)).trans
        (pow_le_pow_left₀ (by norm_num) (by norm_num : (3:ℕ)≤4) _)
      exact_mod_cast hh
    calc
      _ ≤ ((growingMomentDegree t:ℝ)+1)*(4:ℝ)^(bandNewtonDepth t)/slowScale t := by
        apply div_le_div_of_nonneg_right _ ht.le
        exact mul_le_mul_of_nonneg_left hd (by positivity)
      _ = (growingMomentDegree t:ℝ)*(4:ℝ)^(bandNewtonDepth t)/slowScale t+
          (4:ℝ)^(bandNewtonDepth t)/slowScale t := by ring
      _ ≤ _ := add_le_add le_rfl (by
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hn ht.le)

#print axioms growingMomentDegree_newton_cost_sublinear
#print axioms growingMomentDegree_newton_degree_sublinear
end QuantitativeMaass
