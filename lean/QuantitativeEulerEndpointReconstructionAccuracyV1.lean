module

public import QuantitativeEulerEndpointCommonReconstructionCostV1
public import QuantitativeEulerEndpointInitialDoubleExpV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticFiniteBranch

/-- The reconstruction accuracy pays any double-exponential amplification
on the endpoint scale, leaving inverse-scale error. -/
theorem amplified_error_le {K R D : ℝ} (hK : 0≤K) (hR : 1≤R)
    (hD : D≤Real.exp (Real.exp (K*R))) :
    D*(Real.exp (-8*Real.exp ((K+1)*R))/2)≤1/R := by
  let s := Real.exp ((K+1)*R)
  have hR0 : 0<R := by linarith
  have hs0 : 0≤s := (Real.exp_pos _).le
  have hRs : R≤s := by
    have harg : R≤(K+1)*R := by nlinarith
    have hh := Real.add_one_le_exp ((K+1)*R)
    dsimp only [s]
    linarith
  have hKs : Real.exp (K*R)≤s := Real.exp_le_exp.mpr (by nlinarith)
  have he : Real.exp (Real.exp (K*R))*Real.exp (-8*s)≤Real.exp (-R) := by
    rw [←Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hinv : Real.exp (-R)≤1/R := by
    rw [Real.exp_neg,one_div]
    apply (inv_le_inv₀ (Real.exp_pos R) hR0).mpr
    linarith [Real.add_one_le_exp R]
  have hm := mul_le_mul_of_nonneg_right hD (by positivity : 0≤Real.exp (-8*s)/2)
  have he0 := (Real.exp_pos (Real.exp (K*R))).le
  have ht0 := (Real.exp_pos (-8*s)).le
  change D*(Real.exp (-8*s)/2)≤1/R
  nlinarith [hinv,he,mul_nonneg he0 ht0]

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

#print axioms amplified_error_le
#print axioms exists_horizon_cost
end QuantitativeEulerEndpointCommonReconstruction
