module

public import QuantitativeEulerEndpointComparisonBudgetV1
public import QuantitativeMaassRawBoundedActualResidualV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeMaass.RawBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointExponentialParameters
open QuantitativeEulerEndpointNestedPerturbation QuantitativeEulerEndpointResidual
open scoped Classical MatrixGroups

/-- Actual degree and mass estimates bound the operator-comparison budget,
in addition to the previously checked fixed-solution residual budget. -/
theorem exists_actual_comparison_bound {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A)
    (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ) (sector : Sector N)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)
    (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀) (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n : ℕ,
      let b := actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n
      ∀ z : ℕ → ℝ[X],
      (∀ j,j<n → (z j).natDegree≤16*(sharpnessAt A P sector n b (j+1))^5+1) →
      (∀ j,j<n → (∑ i∈(z j).support,|(z j).coeff i|)≤
        (((16*(sharpnessAt A P sector n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P sector n b (j+1))^5)) →
      comparisonBudget (fun i => power (effortAt A P sector n b i)) z n≤Real.exp (Real.exp (K*(4:ℝ)^n)) := by
  obtain ⟨K,hK,hbound⟩ := exists_actual_residual_bound A P hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  refine ⟨K+2,by positivity,?_⟩
  intro n b z hd hm
  have he := hbound n z hd hm
  exact (comparisonBudget_le_square _ z n).trans (squared_double_exp
    (one_le_pow₀ (by norm_num)) (by linarith [errorBudget_ge_one (fun i => power (effortAt A P sector n b i)) z n]) he)

#print axioms exists_actual_comparison_bound
end QuantitativeMaass.RawBoundedIteration
