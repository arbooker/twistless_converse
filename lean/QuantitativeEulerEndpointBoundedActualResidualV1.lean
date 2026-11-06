module

public import QuantitativeEulerEndpointBoundedActualCostV1
public import QuantitativeEulerEndpointResidualCostV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra
open QuantitativeEulerEndpointNestedExpression QuantitativeEulerEndpointExponentialParameters
open scoped Classical MatrixGroups

/-- Uniform double-exponential residual amplification for any sequence
having the degree and mass fields of the actual bounded iteration. -/
theorem exists_actual_residual_bound {N Q : ℕ} [NeZero N] {hQ : 0<Q}
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
      QuantitativeEulerEndpointResidual.errorBudget
        (fun i => power (effortAt A P sector n b i)) z n≤Real.exp (Real.exp (K*(4:ℝ)^n)) := by
  obtain ⟨Kl,hKl,hlog⟩ := exists_actual_logarithmic_cost A P hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  obtain ⟨Kc,hKc,hcoef⟩ := exists_actual_coefficient_bound A P hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  refine ⟨Kl+Kc+16,by positivity,?_⟩
  intro n b z hd hm
  let R : ℝ := (4:ℝ)^n
  let V : ℝ := Real.exp (Real.exp ((Kc+16)*R))
  have hR : 1≤R := one_le_pow₀ (by norm_num)
  have hV : 16≤V := by
    have hc : 16≤(Kc+16)*R := by nlinarith
    dsimp only [V]
    linarith [Real.add_one_le_exp ((Kc+16)*R),Real.add_one_le_exp (Real.exp ((Kc+16)*R))]
  have hc : Kc*R≤(Kc+16)*R := by nlinarith
  have hm' (j : ℕ) (hj : j<n) : (∑ i∈(z j).support,|(z j).coeff i|)≤V :=
    (hcoef n z hm j hj).trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hc))
  have hvlog : Real.log V≤Real.exp ((Kc+16)*R) := by
    dsimp only [V]
    rw [Real.log_exp]
  have hh := QuantitativeEulerEndpointResidual.errorBudget_double_exp
    (fun i => power (effortAt A P sector n b i)) z hV n hm' (hlog n z hd).1 hvlog
  convert hh using 1
  dsimp only [R]
  congr 2
  ring

#print axioms exists_actual_residual_bound
end QuantitativeEulerEndpointBoundedIteration
