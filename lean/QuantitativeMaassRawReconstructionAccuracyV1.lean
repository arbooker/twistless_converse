module

public import QuantitativeMaassRawCommonReconstructionCostV1
public import QuantitativeEulerEndpointInitialDoubleExpV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticFiniteBranch

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- At the accuracy needed by the actual iteration, common reconstruction
still has double-exponential coefficient and matrix costs. -/
theorem exists_horizon_cost (hN : 0<N) {K : ℝ} (hK : 0≤K) :
    ∃ C : ℝ,0≤C ∧ ∀ n : ℕ,∀ e : Sector N,
      let s := Real.exp ((K+1)*(4:ℝ)^n)
      expressionBound (expression A P hN s e)≤Real.exp (Real.exp (C*(4:ℝ)^n)) ∧
      ExpressionMatrixBound (expression A P hN s e) (Real.exp (Real.exp (C*(4:ℝ)^n))) := by
  obtain ⟨C,hC,hbound⟩ := exists_cost_bound A P hN
  refine ⟨C+12*(K+1),by positivity,?_⟩
  intro n e s
  have hR : 1≤(4:ℝ)^n := one_le_pow₀ (by norm_num)
  have hs : 1≤s := Real.one_le_exp_iff.mpr (by positivity)
  have hp : s^12=Real.exp ((12*(K+1))*(4:ℝ)^n) := by
    dsimp only [s]
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hh : C*s^12≤Real.exp ((C+12*(K+1))*(4:ℝ)^n) := by
    rw [hp]
    exact QuantitativeEulerEndpointPolynomialGrowth.scaled_exp_le hC hR
  have he := Real.exp_le_exp.mpr hh
  exact ⟨(hbound s hs e).1.trans he,(hbound s hs e).2.mono he⟩

#print axioms exists_horizon_cost
end QuantitativeMaass.RawCommonReconstruction
