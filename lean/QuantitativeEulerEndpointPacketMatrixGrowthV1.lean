module

public import QuantitativeEulerEndpointWideGramExpressionV1
public import QuantitativeEulerEndpointInitialExpressionGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open QuantitativeEulerEndpointInitialExpression

theorem packetMatrixBound_polynomial (N : ℕ) (R Y H U : ℝ) (l : List (EligiblePrime N))
    (hU : 1≤U) (hN : (N:ℝ)≤U) (hlen : (l.length:ℝ)≤U) (hq : ∀ q∈l,(q.val:ℝ)≤U)
    (hR0 : 0≤R) (hR : R≤U) (hH0 : 0≤H) (hH : H≤U)
    (hY : 0<Y) (hYinv : (min 1 Y)⁻¹≤U) :
    packetMatrixBound N R Y H l≤36*U^11 := by
  have hU0 : 0≤U := by linarith
  have hrow (i : Fin l.length) :
      4*(1+(wideCompactCutoff (N*l[i.val].val^3:ℕ) R Y H:ℝ))*(N*l[i.val].val^3:ℕ)≤36*U^10 := by
    have hq' : (l[i.val].val:ℝ)≤U := hq _ (List.getElem_mem i.isLt)
    have hB : ((N*l[i.val].val^3:ℕ):ℝ)≤U^4 := by
      push_cast
      calc
        _ ≤ U*U^3 := mul_le_mul hN (pow_le_pow_left₀ (by positivity) hq' 3) (by positivity) hU0
        _ = _ := by ring
    exact wide_matrix_polynomial _ R Y H U hU (by positivity) hB hR0 hR hH0 hH hY hYinv
  have h := sum_uniform _ (by simpa only [Fintype.card_fin] using hlen)
    (by positivity : 0≤36*U^10) hrow
  apply h.trans_eq
  ring

#print axioms packetMatrixBound_polynomial
end QuantitativeEulerEndpointPrepared
