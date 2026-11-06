module

public import QuantitativeEulerEndpointComparisonIterationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointExponentialParameters
open QuantitativeEulerEndpointNestedPerturbation QuantitativeEulerEndpointCommonReconstruction
open QuantitativeHolomorphic AsymptoticFiniteBranch
open scoped Classical MatrixGroups

/-- One actual common finite expression pays the full operator-comparison
budget of the bounded prime iteration in both representations, with uniform
double-exponential coefficient and matrix cost. Polynomial hypotheses are
exactly the degree and mass fields already proved by Step. -/
theorem exists_paid_common_reconstruction {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A)
    (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ) (sector : Sector N)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)
    (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀) (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K C' : ℝ,0≤K ∧ 0≤C' ∧ ∀ n : ℕ,
      let b := actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n
      let E := expression A P (NeZero.pos N) (Real.exp ((K+1)*(4:ℝ)^n)) sector
      expressionBound E≤Real.exp (Real.exp (C'*(4:ℝ)^n)) ∧
      ExpressionMatrixBound E (Real.exp (Real.exp (C'*(4:ℝ)^n))) ∧
      (∀ x,‖regularSum E x‖≤1) ∧ (∀ h,‖holomorphicSum E (h+1)‖≤1) ∧
      ∀ z : ℕ → ℝ[X],
      (∀ j,j<n → (z j).natDegree≤16*(sharpnessAt A P sector n b (j+1))^5+1) →
      (∀ j,j<n → (∑ i∈(z j).support,|(z j).coeff i|)≤
        (((16*(sharpnessAt A P sector n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P sector n b (j+1))^5)) →
      let V := comparisonBudget (fun i => power (effortAt A P sector n b i)) z n
      (∀ x,V*‖regularSum E x-normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P sector x‖≤1/(4:ℝ)^n) ∧
      (∀ h,V*‖holomorphicSum E (h+1)-
        AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
          ((normalizedCountReconstruction A (NeZero.pos N) P h sector).comp
            (AsymptoticCylinderTerminal.ambientLift
              (AsymptoticReconstructedCount.parameters A P).ε).adjoint)‖≤1/(4:ℝ)^n) := by
  obtain ⟨K,hK,hbudget⟩ := exists_actual_comparison_bound A P hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  obtain ⟨C',hC',hcost⟩ := exists_horizon_cost A P (NeZero.pos N) hK
  refine ⟨K,C',hK,hC',?_⟩
  intro n b E
  have hc := hcost n sector
  refine ⟨hc.1,hc.2,regular_norm A P (NeZero.pos N) _ sector,
    physical_norm A P (NeZero.pos N) _ sector,?_⟩
  intro z hd hm V
  have hv : V≤Real.exp (Real.exp (K*(4:ℝ)^n)) := hbudget n z hd hm
  have hv0 : 0≤V := by linarith [comparisonBudget_ge_one (fun i => power (effortAt A P sector n b i)) z n]
  have hpaid := amplified_error_le hK (one_le_pow₀ (by norm_num)) hv
  exact ⟨fun x => (mul_le_mul_of_nonneg_left (regular_error A P (NeZero.pos N) _ sector x) hv0).trans hpaid,
    fun h => (mul_le_mul_of_nonneg_left (physical_error A P (NeZero.pos N) _ sector h) hv0).trans hpaid⟩

#print axioms exists_paid_common_reconstruction
end QuantitativeEulerEndpointBoundedIteration
