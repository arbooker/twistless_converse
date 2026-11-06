module

public import QuantitativeArithmeticRetainedExpressionComparisonV1
public import QuantitativeArithmeticRetainedScheduleGrowthV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedCommonExpression
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFiniteTransport QuantitativeArithmeticRetainedScheduleGrowth
open AsymptoticSectorSigns AsymptoticFiniteBranch QuantitativeHolomorphic

variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q}
  (A : Certificate N R₀ Q hQ) (P : Parameters A)
  (hR₀ : ∀p∈R₀,p.Prime) (hN : 0<N)

/-- The same common approximation used in the perturbation argument is
exactly the already costed reconstruction at logarithmic accuracy 8s+log2. -/
theorem expression_eq_scheduled (s : ℝ) (e : Sector N) :
    expression A P hR₀ hN s e=
      normalizedExpression A P hR₀ hN (accuracy (8*s+Real.log 2)) e := by
  unfold expression accuracy
  congr 1
  rw [neg_add,Real.exp_add,Real.exp_neg (Real.log 2),Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [show -(8*s) = -8*s by ring]
  ring

/-- Uniform coefficient, length, and matrix-height costs for the actual
common expression; the constant is fixed before sector or weight. -/
theorem uniform_common_cost : ∃C : ℝ,1≤C ∧ ∀s : ℝ,1≤s → ∀e : Sector N,
    expressionBound (expression A P hR₀ hN s e)≤Real.exp (C*s^6) ∧
    ((expression A P hR₀ hN s e).length:ℝ)≤Real.exp (C*s^6) ∧
    ExpressionMatrixBound (expression A P hR₀ hN s e) (Real.exp (C*s^6)) := by
  obtain ⟨C,hC,hcost⟩ := uniform_cost A P hR₀ hN
  let a : ℝ := 8+Real.log 2
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have ha : 1≤a := by dsimp only [a]; linarith
  have ha6 : 1≤a^6 := one_le_pow₀ ha
  refine ⟨C*a^6,(le_mul_of_one_le_right (zero_le_one.trans hC) ha6).trans' hC,?_⟩
  intro s hs e
  have hu : 1≤8*s+Real.log 2 := by linarith
  have hb : 8*s+Real.log 2≤a*s := by
    have := mul_le_mul_of_nonneg_left hs hl
    dsimp only [a]
    nlinarith
  have hp := pow_le_pow_left₀ (zero_le_one.trans hu) hb 6
  have he : Real.exp (C*(8*s+Real.log 2)^6)≤Real.exp ((C*a^6)*s^6) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hp (zero_le_one.trans hC)
    simpa only [mul_pow,mul_assoc] using this
  rw [expression_eq_scheduled]
  have hh := hcost (8*s+Real.log 2) hu e
  exact ⟨hh.1.trans he,hh.2.1.trans he,hh.2.2.1.mono he⟩

#print axioms expression_eq_scheduled
#print axioms uniform_common_cost

/-- The accuracy needed by the complete finite iteration retains a
uniform double-exponential bound at the geometric horizon. -/
theorem exists_horizon_cost {K : ℝ} (hK : 0≤K) :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀e : Sector N,
      let s := Real.exp ((K+1)*(4:ℝ)^n)
      expressionBound (expression A P hR₀ hN s e)≤Real.exp (Real.exp (C*(4:ℝ)^n)) ∧
      ExpressionMatrixBound (expression A P hR₀ hN s e) (Real.exp (Real.exp (C*(4:ℝ)^n))) := by
  obtain ⟨C,hC,hbound⟩ := uniform_common_cost A P hR₀ hN
  have hC0 := zero_le_one.trans hC
  refine ⟨C+6*(K+1),by positivity,?_⟩
  intro n e s
  have hR : 1≤(4:ℝ)^n := one_le_pow₀ (by norm_num)
  have hs : 1≤s := Real.one_le_exp_iff.mpr (by positivity)
  have hp : s^6=Real.exp ((6*(K+1))*(4:ℝ)^n) := by
    dsimp only [s]
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hh : C*s^6≤Real.exp ((C+6*(K+1))*(4:ℝ)^n) := by
    rw [hp]
    exact QuantitativeEulerEndpointPolynomialGrowth.scaled_exp_le hC0 hR
  have he := Real.exp_le_exp.mpr hh
  exact ⟨(hbound s hs e).1.trans he,(hbound s hs e).2.2.mono he⟩

#print axioms exists_horizon_cost
end QuantitativeArithmeticRetainedCommonExpression
