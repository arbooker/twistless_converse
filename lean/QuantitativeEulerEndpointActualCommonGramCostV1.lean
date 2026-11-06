module

public import QuantitativeEulerEndpointActualGramExponentialV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticFiniteBranch
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem exists_actual_common_gram_cost (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) {K : ℝ} (hK : 0≤K) :
    ∃ C' : ℝ,0≤C' ∧ ∀ n j : ℕ,j≤n →
      let E := QuantitativeEulerEndpointCommonReconstruction.expression A P (NeZero.pos N)
        (Real.exp ((K+1)*(4:ℝ)^n)) e
      let g := actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n E j
      expressionBound g≤Real.exp (Real.exp (C'*(4:ℝ)^n)) ∧
      ExpressionMatrixBound g (Real.exp (Real.exp (C'*(4:ℝ)^n))) := by
  obtain ⟨a,ha,hrows⟩ := exists_actual_gram_exponential A P e hN excluded threshold S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0
  obtain ⟨c,hc,hrecon⟩ := QuantitativeEulerEndpointCommonReconstruction.exists_horizon_cost A P (NeZero.pos N) hK
  refine ⟨a+c+3,by positivity,?_⟩
  intro n j hj E g
  have hu := hrecon n e
  have hg := hrows n j hj E (Real.exp (Real.exp (c*(4:ℝ)^n))) (Real.exp_pos _).le hu.1 hu.2
  have hs := exp_times_double_exp_square ha hc (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n))
  exact ⟨hg.1.trans hs,hg.2.mono hs⟩

#print axioms exists_actual_common_gram_cost
end QuantitativeEulerEndpointBoundedIteration
