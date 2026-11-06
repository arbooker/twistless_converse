module

public import QuantitativeEulerEndpointBoundedActualDataV1
public import QuantitativeEulerEndpointScheduledExpressionCostV1
public import QuantitativeEulerEndpointInitialDoubleExpV1

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra
open QuantitativeEulerEndpointNestedExpression QuantitativeEulerEndpointExponentialParameters
open scoped Classical MatrixGroups

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
  (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ) (sector : Sector N)
  (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
  (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)
local notation "area" => (AsymptoticReconstructedCount.parameters A P).ε⁻¹

/-- A uniform logarithmic degree/depth budget for the actual explicitly
normalized blocks. The hypotheses on z are exactly the degree fields
retained by the constructed regular iteration. -/
theorem exists_actual_logarithmic_cost (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n : ℕ,
      let b := actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n
      ∀ z : ℕ → ℝ[X],
      (∀ j,j<n → (z j).natDegree≤16*(sharpnessAt A P sector n b (j+1))^5+1) →
      (∑ j∈Finset.range n,logarithmicCost (fun i => power (effortAt A P sector n b i)) z j)≤K*(4:ℝ)^n ∧
      (budget (fun i => power (effortAt A P sector n b i)) z n:ℝ)≤Real.exp (K*(4:ℝ)^n) := by
  obtain ⟨K,hK,hbound⟩ := exists_actual_total_effort A P hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  have ha : 0≤area := inv_nonneg.mpr (AsymptoticReconstructedCount.parameters A P).epsilon_pos.le
  refine ⟨scheduleConstant area+17*K,add_nonneg (scheduleConstant_nonneg ha) (by positivity),?_⟩
  intro n b z hz
  have hE (j : ℕ) (_hj : j≤n) : 0≤effortAt A P sector n b j :=
    (actualBlock_effort_pos A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs hK0 n j).le
  have hsum := scheduled_cost_geometric n (effortAt A P sector n b) z ha hE hz (hbound n)
  exact ⟨hsum,budget_le_exp _ z n hsum⟩

#print axioms exists_actual_logarithmic_cost

/-- Every scheduled sharpening has a common exponential envelope in the
horizon, derived from the already proved total effort. -/
theorem exists_actual_sharpness_bound (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n j : ℕ,j≤n →
      (sharpnessAt A P sector n
        (actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n) j:ℝ)+1≤
          Real.exp (K*(4:ℝ)^n) := by
  obtain ⟨K,hK,hbound⟩ := exists_actual_total_effort A P hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  have ha : 0≤area := inv_nonneg.mpr (AsymptoticReconstructedCount.parameters A P).epsilon_pos.le
  refine ⟨280*area+3+3*K,by positivity,?_⟩
  intro n j hj
  let b := actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n
  let E := effortAt A P sector n b
  have hE (i : ℕ) : 0≤E i :=
    (actualBlock_effort_pos A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs hK0 n i).le
  have hs : 0≤∑ i∈Finset.range n,E i := Finset.sum_nonneg (fun i _ => hE i)
  have he : E j≤K*(4:ℝ)^n := by
    have ht := hbound n
    change (∑ i∈Finset.range n,E i)+E n≤K*(4:ℝ)^n at ht
    rcases eq_or_lt_of_le hj with rfl | hj
    · linarith
    · have hi := Finset.single_le_sum (fun i (_hi : i∈Finset.range n) => hE i) (Finset.mem_range.mpr hj)
      linarith [hE n]
  have hh := sharpness_exp_upper ha (hE j)
  have he' := Real.exp_le_exp.mpr (show 3*E j≤(3*K)*(4:ℝ)^n by nlinarith)
  have hc : 0≤280*area+3 := by positivity
  exact hh.trans ((mul_le_mul_of_nonneg_left he' hc).trans
    (QuantitativeEulerEndpointPolynomialGrowth.scaled_exp_le hc (one_le_pow₀ (by norm_num))))

/-- All outgoing sharpening coefficient masses have a common double
exponential bound; the hypothesis is the actual retained mass field. -/
theorem exists_actual_coefficient_bound (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n : ℕ,
      let b := actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n
      ∀ z : ℕ → ℝ[X],
      (∀ j,j<n → (∑ i∈(z j).support,|(z j).coeff i|)≤
        (((16*(sharpnessAt A P sector n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P sector n b (j+1))^5)) →
      ∀ j,j<n → (∑ i∈(z j).support,|(z j).coeff i|)≤Real.exp (Real.exp (K*(4:ℝ)^n)) := by
  obtain ⟨K,hK,hbound⟩ := exists_actual_sharpness_bound A P hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  refine ⟨QuantitativeEulerEndpointPolynomialGrowth.initialBaseConstant K,?_,?_⟩
  · unfold QuantitativeEulerEndpointPolynomialGrowth.initialBaseConstant
    positivity
  intro n b z hz j hj
  exact (hz j hj).trans (QuantitativeEulerEndpointPolynomialGrowth.sharpening_coefficient_double_exp
    hK (one_le_pow₀ (by norm_num)) (hbound n (j+1) hj))

#print axioms exists_actual_sharpness_bound
#print axioms exists_actual_coefficient_bound
end QuantitativeEulerEndpointBoundedIteration
