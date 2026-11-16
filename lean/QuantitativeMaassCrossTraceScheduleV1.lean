module

public import QuantitativeMaassStrongMomentScheduleV1
public import QuantitativeHolomorphicExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter AsymptoticFiniteBranch QuantitativeHolomorphic
open scoped Topology
namespace QuantitativeMaass.Strong

/-- The finite-expression geometric error vanishes on the actual degree
and window schedules, including any fixed strong-scale exponential weight.
Coefficient and height costs are retained explicitly. -/
theorem finite_expression_geometric_cost_limit
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (E : ℝ → Expression) (B R L : ℝ → ℝ)
    (G H U C W : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H) (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hcost : ∀ᶠ t in atTop,
      expressionBound (E t) ≤ Real.exp (G*(growingLVDegree t:ℝ)+H*strongScale t) ∧
      0 ≤ B t ∧ B t ≤ Real.exp (G*(growingLVDegree t:ℝ)+H*strongScale t))
    (hgeometry : ∀ᶠ t in atTop, R t ≤ H*strongScale t ∧ L t ≤ H*strongScale t) :
    Tendsto (fun t => Real.exp (W*strongScale t)*expressionBound (E t)*
      (1+4*B t)^40*C*Real.sqrt t*(ε t)^2*Real.exp (U*R t+30*L t)/(t*ε t))
      atTop (𝓝 0) := by
  have hlim := weighted_growingMomentDegree_cost ε (Real.exp (41*G)) (5^40*C)
    (W+(U+71)*H) (Real.exp_pos _) (by positivity)
    (hε.mono (fun _ h => h.1)) hp
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ),hcost] with t he ht hc
    have hE0 := expressionBound_nonneg (E t)
    have hB0 := hc.2.1
    exact div_nonneg (by positivity) (mul_nonneg ht.le he.1.le)
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ),hcost,hgeometry] with t he ht hc hg
    have hcoeff := hc.1
    have hB0 := hc.2.1
    let X := G*(growingLVDegree t:ℝ)+H*strongScale t
    have hX : 0 ≤ X := add_nonneg (mul_nonneg hG (Nat.cast_nonneg _))
      (mul_nonneg hH (sq_nonneg _))
    have hx : 1 ≤ Real.exp X := Real.one_le_exp_iff.mpr hX
    have hb : 1+4*B t ≤ 5*Real.exp X := by nlinarith [hc.2.2]
    have heps : (ε t)^2 ≤ 1 := by nlinarith [he.1,he.2]
    have hrad : Real.exp (U*R t+30*L t) ≤
        Real.exp ((U+30)*H*strongScale t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hg.1 hU]
    apply div_le_div_of_nonneg_right _ (mul_nonneg ht.le he.1.le)
    calc
      _ ≤ Real.exp (W*strongScale t)*Real.exp X*(5*Real.exp X)^40*C*
          Real.sqrt t*1*Real.exp ((U+30)*H*strongScale t) := by
        gcongr
      _ = Real.exp ((W+(U+71)*H)*strongScale t)*(5^40*C)*Real.sqrt t*
          (Real.exp (41*G))^(growingLVDegree t) := by
        rw [mul_pow,←Real.exp_nat_mul,←Real.exp_nat_mul]
        norm_num only [Nat.cast_ofNat]
        have hexp : Real.exp (W*strongScale t)*Real.exp X*
            Real.exp (40*X)*Real.exp ((U+30)*H*strongScale t) =
            Real.exp ((W+(U+71)*H)*strongScale t)*
              Real.exp ((growingLVDegree t:ℝ)*(41*G)) := by
          rw [←Real.exp_add,←Real.exp_add,←Real.exp_add,←Real.exp_add]
          congr 1
          dsimp only [X]
          ring
        calc
          _ = (5^40*C*Real.sqrt t)*(Real.exp (W*strongScale t)*Real.exp X*
              Real.exp (40*X)*Real.exp ((U+30)*H*strongScale t)) := by ring
          _ = _ := by rw [hexp]; ring

#print axioms finite_expression_geometric_cost_limit

end QuantitativeMaass.Strong
